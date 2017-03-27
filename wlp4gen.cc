#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <map>
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <set>
using namespace std;
const string S = "start";
const string proc = "procedure";
const string procs = "procedures";
const string ma = "main";
const string wa = "wain";
const string ID = "ID";
const string myleaf[] = {"ID", "BOF", "BECOMES", "COMMA", "ELSE", "EOF", "EQ", "GE", "GT", "IF", "INT", "LBRACE", "LE", "LPAREN", "LT", "MINUS", "NE", "NUM", "PCT", "PLUS", "PRINTLN", "RBRACE", "RETURN", "RPAREN", "SEMI", "SLASH", "STAR", "WAIN", "WHILE", "AMP", "LBRACK", "RBRACK", "NEW", "DELETE", "NULL"};//size 35 w/ id
const set <string> leaves (myleaf,myleaf+35);
struct Node{
    string name;
    string val;
    string rule;
    vector<string > tokenlist;
    vector<Node* > child;
    string tp;//only for expr/term
    //int numkid;
    Node(string name,string rule,vector<string > tokenlist):name(name),rule(rule),tokenlist(tokenlist){
        tp = "uk";
    }
};
string exist(map<string,string > m,string s){
    string found;
    if ((int)m.size()>0) {
        map<string,string>::iterator it;
        for (it = m.begin(); it != m.end(); ++it){
            if(it->second == s){
                found = it->first;
                break;
            }
        }
    }
    return found;
}
void clean(Node *n){
    int size = (int)n->child.size();
    if (size > 0) {
        for(int i = 0; i < size; i++){
            clean(n->child.at(i));
        }
        delete n;
    }else{
        delete n;
    }
    return;
}
void printWrapper(map<string, pair<vector<string>,map <string, string > > > m){
    map<string, pair<vector<string>,map <string, string > > >::iterator it;
    for (it = m.begin(); it != m.end(); ++it){
        cerr << it->first;
        vector<string > v = it->second.first;
        for (vector<string >::iterator it1 = v.begin(); it1 != v.end(); ++it1) {
            cerr << " " << *it1;
        }
        cerr << endl;
        pair<vector<string>,map <string, string > > p = it->second;
        for (map<string,string>::iterator it = p.second.begin(); it != p.second.end(); ++it){
            cerr << it->first << " " << it->second << endl;
        }
        cerr << endl;
    }
}
void printVec(vector<string> v){
    for (vector<string>::iterator it = v.begin(); it != v.end(); it++) {
        cout << *it <<" ";
    }
    cout << endl;
}
void readIn(istream &in, Node* parent){
    string line, tok,temp;
    getline(cin, line);
    istringstream is(line);
    vector<string> tokenline;
    is >> tok;
    Node * curr = new Node(tok,line,tokenline);
    parent->child.push_back(curr);
    while(true){
        is >> tok;
        if (is.fail())break;
        if(leaves.count(tok)>0){
            string name,val,tmpline;
            getline(in,tmpline);
            istringstream iss(tmpline);
            iss >> name;
            iss >> val;
            curr->tokenlist.push_back(val);
        }else{
            readIn(in, curr);
        }
    }
}
//globals
map<string, pair<vector<string>,map <string, string > > > symMaps;
map<string, map<string,pair<int,string> > > symTab;//<procname,map<id,pair<offset,type>>>
vector<string> params;
map<string, string> subSymTab;
string procname;
bool hasParam = true;
map<string,vector<string > > CallingMap;
vector<string> callingParam;
vector<string> callingProcStack;
int currInd = 0;
int looptime = 0;
int ifelsetime = 0;
void getType(Node* n){
    //traverse and add type
    if ((int)n->child.size()>0){
        for (vector<Node* >::iterator it = n->child.begin(); it != n->child.end(); ++it) {
            getType(*it);
        }
    }
    ///////////////////////////////////////////////////////////
    if(n->name == "type"){
        //cout << "get type"<<endl;
        //printVec(n->tokenlist);
        if (n->rule=="type INT") {
            n->tp = "int";
        }else{
            n->tp = "int*";
        }
    }
    if(n->name == "main"){
        //cout << "get main"<<endl;
        if (n->rule == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
            if (n->child.at(1)->tp != "int") {
                cout << "second param of main :" << n->child.at(1)->tp << endl;
                cerr << "ERROR! second param of main not int!"<<endl;
            }else{
                if (n->child.back()->tp != "int") {
                    cerr << "ERROR! main not returning int!"<<endl;
                }else{
                    procname = wa;
                    n->tp = "int";
                }
            }
        }
    }
    if(n->name == "procedure"){
        if (n->rule == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
            if (n->child.back()->tp != "int") {
                cerr << "ERROR! proc not returning int!"<<endl;
            }else{
                procname = n->tokenlist.at(1);
                n->tp = "int";
            }
        }
    }
    if(n->name == "dcl"){
        n->tp = n->child.front()->tp;
    }
    if (n->name == "dcls") {
        if (n->rule == "dcls dcls dcl BECOMES NUM SEMI") {
            //cout << "initial val to " << n->child.back()->child.front()->tokenlist.front()<<" ("<< n->child.back()->tp<<endl;
            if (n->child.back()->tp != "int") {
                cerr << "ERROR! initial int value to non int!"<<endl;
            }
        }else if(n->rule == "dcls dcls dcl BECOMES NULL SEMI"){
            //cout << "initial val to "<< n->child.back()->child.front()->tokenlist.front()<<" (" << n->child.back()->tp<<endl;
            if (n->child.back()->tp != "int*") {
                cerr << "ERROR! initial int* value to non int*!"<<endl;
            }
        }
    }
    if (n->name =="expr") {
        if (n->rule == "expr term") {
            n->tp = n->child.front()->tp;
        }else if(n->rule == "expr expr PLUS term"){
            if (n->child.front()->tp == "int" && n->child.back()->tp == "int") {
                n->tp = n->child.front()->tp;
            }else if(n->child.front()->tp == "int*" && n->child.back()->tp == "int"){
                n->tp = n->child.front()->tp;
            }else if(n->child.front()->tp == "int" && n->child.back()->tp == "int*"){
                n->tp = n->child.back()->tp;
            }else{
                cerr << "ERROR! int* + int*"<<endl;
            }
        }else if(n->rule == "expr expr MINUS term"){
            if (n->child.front()->tp == "int*" && n->child.back()->tp == "int") {
                n->tp = "int*";
            }else if((n->child.front()->tp == "int*" && n->child.back()->tp == "int*")||(n->child.front()->tp == "int" && n->child.back()->tp == "int")){
                n->tp = "int";
            }else{
                cerr << "ERROR! int - int*"<<endl;
            }
        }else{
            //cout <<"?????"<<endl;
        }
    }
    if(n->name =="term"){
        if (n->rule == "term factor") {
            n->tp = n->child.front()->tp;
        }else if(n->rule == "term term STAR factor"){
            if (n->child.front()->tp == "int" && n->child.back()->tp == "int") {
                n->tp = "int";
            }else{
                cerr << "ERROR! * "<<endl;
            }
        }else if(n->rule == "term term SLASH factor"){
            if (n->child.front()->tp == "int" && n->child.back()->tp == "int") {
                n->tp = "int";
            }else{
                cerr << "ERROR! / "<<endl;
            }
        }else if(n->rule == "term term PCT factor"){
            if (n->child.front()->tp == "int" && n->child.back()->tp == "int") {
                n->tp = "int";
            }else{
                cerr << "ERROR! % "<<endl;
            }
        }
    }
    if(n->name =="lvalue"){
        if(n->rule == "lvalue STAR factor"){
            //cout << "get tp from * fac "<< endl;
            if (n->child.front()->tp == "int*") {
                n->tp = "int";
            }else{
                cerr << "ERROR * on int "<<endl;
            }
        }else if(n->rule == "lvalue LPAREN lvalue RPAREN"){
            n->tp = n->child.front()->tp;
        }
    }
    if(n->name == "factor"){
        if(n->rule == "factor NUM"){
            //cout << "get tp num for fac "<< endl;
            n->tp = "int";
        }else if(n->rule == "factor NULL"){
            //cout << "get tp null for fac "<< endl;
            n->tp = "int*";
        }else if(n->rule == "factor LPAREN expr RPAREN"){
            //cout << "get tp (expr) for fac "<< endl;
            n->tp = n->child.front()->tp;
        }else if(n->rule == "factor AMP lvalue"){
            if (n->child.front()->tp == "int") {
                n->tp = "int*";
            }else{
                cerr <<  "ERROR & before non int"<<endl;
            }
        }else if(n->rule == "factor STAR factor"){
            //cout << "get tp * fac "<< endl;
            if (n->child.front()->tp == "int*") {
                n->tp = "int";
                return;
            }else{
                cerr << "ERROR with * before int" <<endl;
            }
        }else if(n->rule == "factor NEW INT LBRACK expr RBRACK"){
            //cout << "get tp new int [expr] for fac "<< endl;
            if (n->child.front()->tp == "int") {
                n->tp = "int*";
            }else{
                string s = "ERROR with new int[] before non int";
                cerr << s<<endl;
            }
        }else if(n->rule == "factor ID LPAREN RPAREN"){
            //cout << "get tp id() for fac "<< endl;
            string id = n->tokenlist.front();
            if (symMaps.count(id)&&(int)symMaps[id].first.size()==0) {
                n->tp = "int";
            }else{
                cerr << "ERROR with calling 0 param function failure"<<endl;
            }
        }else if(n->rule == "factor ID LPAREN arglist RPAREN"){
            string id = n->tokenlist.front();
            int num =(int)symMaps[id].first.size();
            if (num != (int)callingParam.size()) {
                cerr << "ERROR param number not matching! " << num << " and " << (int)callingParam.size() <<endl;
                
            }else{
                bool check = true;
                for (int i = num - 1; i >= 0; i--) {
                    if (symMaps[id].first.at(i) != callingParam.at(i)){
                        check=false;
                        break;
                    }
                }
                if(check){
                    n->tp = "int";
                }else{
                    cerr << "ERROR param kind not matching!"<<endl;
                }
            }
            callingParam.clear();
        }
    }
    if(n->name == "arglist"){//filling callingParam
        if (n->rule == "arglist expr") {
            //cout << "check args add " << n->child.front()->tp<<endl;
            callingParam.insert(callingParam.begin(),n->child.front()->tp);
            //cout << "add tp " << n->child.front()->tp<<endl;
            // n->tp.append(n->child.back()->tp);
        }else if(n->rule == "arglist expr COMMA arglist"){
            //cout << "check args lists " << n->child.front()->tp<<endl;
            callingParam.insert(callingParam.begin(),n->child.front()->tp);
        }
    }
    if (n->name == "statement") {
        if (n->rule == "statement PRINTLN LPAREN expr RPAREN SEMI") {
            if (n->child.front()->tp != "int") {
                cerr << "ERROR! println type not int!"<< endl;
            }
        }else if (n->rule == "statement DELETE LBRACK RBRACK expr SEMI") {
            if (n->child.front()->tp != "int*") {
                cerr << "ERROR! delete type not int*!"<< endl;
            }
        }else if(n->rule == "statement lvalue BECOMES expr SEMI"){
            if (n->child.front()->tp != n->child.back()->tp) {
                cerr << "ERROR! assign diff types!"<< endl;
            }
        }
    }
    if (n->name == "test") {
        if (n->rule == "test expr EQ expr"||n->rule == "test expr NE expr"||
            n->rule == "test expr LT expr"||n->rule == "test expr LE expr"||
            n->rule == "test expr GT expr"||n->rule == "test expr GE expr") {
            if (n->child.front()->tp != n->child.back()->tp) {
                cerr << "ERROR! compare diff type data"<< endl;
            }
        }
    }
}
void traverse(Node* root){
    string rule = root->rule;
    istringstream iss(root->rule);
    if (rule == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        procname = wa;
        hasParam = false;
        if (!symMaps.count(procname)) {
            symMaps.insert(pair<string, pair< vector<string> ,map <string, string> > >(procname, make_pair(params, subSymTab)));
        }else{
            cerr << "ERROR with redefinition of main"<<endl;
        }
    }
    if (rule == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        procname = root->tokenlist.at(1);
        hasParam = false;
        if (!symMaps.count(procname)) {
            symMaps.insert(pair<string, pair< vector<string> ,map <string, string> > >(procname, make_pair(params, subSymTab)));
        }else{
            string s = "ERROR with redefinition of proc ";
            s.append(procname);
            cerr << s<<endl;
        }
    }
    if (root->name == "dcls") {
        hasParam = true;
    }
    if (rule == "dcl type ID") {
        //cout << "in proc "<< procname << endl;
        if (symMaps[procname].second.count(root->tokenlist.front())&&
            root->tokenlist.front()!=procname) {
            string s = "ERROR with redefinition of ";
            s.append(root->tokenlist.front());
            cerr << s <<endl;
        }else{
            string type;
            if (root->child.front()->rule == "type INT STAR") {
                type = "int*";
            }else if(root->child.front()->rule == "type INT"){
                type = "int";
            }
            root->tp = type;
            symMaps[procname].second.insert(pair<string,string>(root->tokenlist.front(),type));
            //for params
            if (!hasParam) {
                //cout << "add "<< root->tokenlist.front() << " to params" << endl;
                symMaps[procname].first.push_back(type);
            }
        }
    }else if(rule == "factor ID"||rule == "lvalue ID"){
        //in current scop with procname(unique) id exist?
        //cout << "read exist id "<<root->tokenlist.front()<<endl;
        if(!symMaps[procname].second.count(root->tokenlist.front())){
            string s = "ERROR with not exist id ";
            s.append(root->tokenlist.front());
            cerr << s <<endl;
        }else{
            
            root->tp = symMaps[procname].second[root->tokenlist.front()];
            //cout << "add type of "<< root->tokenlist.front() << " as " << root->tp<<endl;
        }
    }else if(rule == "factor ID LPAREN RPAREN"||rule == "factor ID LPAREN arglist RPAREN"){
        //has this func name?
        string id = root->tokenlist.front();
        if (!symMaps.count(id)) {
            string s = "ERROR with invalid function of ";
            s.append(id);
            cerr << s <<endl;
        }
        if (symMaps[procname].second.count(id)) {
            string s = "ERROR with invalid call of ";
            s.append(root->tokenlist.front());
            cerr << s <<endl;
        }
    }
    if ((int)root->child.size()>0) {
        for (vector<Node* >::iterator it = root->child.begin(); it != root->child.end(); ++it) {
            traverse(*it);
        }
    }
}
void push(int i){
    cout << "sw $"<<i<<", -4($30) ;push temp result to stack top"<<endl;
    cout << "sub $30,$30,$4 ;update $30"<<endl;
}
void pop(int i){
    cout << "add $30,$30,$4"<<endl;
    cout << "lw $" << i <<",-4($30)"<<endl;
}
void gen(Node* n){
    string name = n->name;
    string rule = n->rule;
    if (rule == "procedures main") {
        map<string,pair<int,string> > submap;
        symTab.insert(pair<string,map<string,pair<int,string> > >(wa,submap));
        gen(n->child.front());
    }else if(rule == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        cout << ";prologue"<<endl;
        cout << "lis $4"<<endl;
        cout << ".word 4"<<endl;
        cout << "lis $11"<<endl;
        cout << ".word 1"<<endl;
        cout << "lis $0"<<endl;
        cout << ".word 0"<<endl;
        cout << "add $29, $30, $0"<<endl;
        cout << "sub $30, $30, $4"<<endl;
        cout << "add $5,$0,$0 ;initial $5 for storing value"<<endl;
        
        //first param
        currInd++;
        string tp1 = n->child.front()->tp;
        symTab[procname].insert(pair<string, pair<int,string> >(n->child.front()->tokenlist.back(), make_pair(currInd, tp1)));
        cout << "sw $1, -4($29)"<<endl;
        cout << "sub $30, $30, $4"<<endl;
        //second param
        currInd++;
        string tp2 = n->child.at(1)->tp;
        symTab[procname].insert(pair<string, pair<int,string> >(n->child.at(1)->tokenlist.back(), make_pair(currInd, tp2)));
        cout << "sw $2, -8($29)"<<endl;
        cout << "sub $30, $30, $4"<<endl;
        //
        gen(n->child.at(2));//dcls
        gen(n->child.at(3));//statements
        gen(n->child.at(4));//expr
        //
        cout << ";epilogue"<<endl;
        for (int i = 0; i < currInd; ++i) {
            cout<<"add $30, $30, $4 ;pop"<<endl;
        }
        cout << "jr $31"<<endl;
    }else if (rule == "type INT") {
        
    }else if (rule == "expr term") {
        gen(n->child.front());
    }else if (rule == "term factor") {
        gen(n->child.front());
    }else if(rule == "factor ID"){
        string idname = n->tokenlist.front();
        int addr = symTab[procname][idname].first;
        cout << "lw $3, -"<<addr*4<<"($29)"<< ";read in addr of id "<< idname << " is "<< addr<<endl;
    }else if(rule == "factor LPAREN expr RPAREN"){
        cout <<"; parens ("<<endl;
        gen(n->child.front());
        cout <<"; parens )"<<endl;
    }else if (rule == "expr expr PLUS term"){/// +
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "add $3, $6, $3"<< endl;
    }else if(rule == "expr expr MINUS term"){/// -
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "sub $3, $6, $3"<< endl;
    }else if(rule == "term term STAR factor"){/// *
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "mult $3, $6"<< endl;
        cout << "mflo $3"<< endl;
    }else if(rule == "term term SLASH factor"){/// /
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "div $6, $3"<< endl;
        cout << "mflo $3"<< endl;
    }else if(rule == "term term PCT factor"){//// %
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "div $6, $3"<< endl;
        cout << "mfhi $3"<< endl;
    }else if(rule == "factor NUM"){
        cout << "lis $3"<<endl;
        cout << ".word "<<n->tokenlist.front()<<endl;
        //cout << ";put number "<<n->tokenlist.front()<<endl;
    }else if(rule == "statements statements statement"){
        gen(n->child.front());
        gen(n->child.at(1));
    }else if(rule == "statements "){
        return;
    }else if(rule == "statement PRINTLN LPAREN expr RPAREN SEMI"){
        gen(n->child.front());
        push(31);
        cout <<"add $1,$3,$0"<<endl;
        cout<< "lis $10"<<endl;
        cout<< ".word print"<<endl;
        cout << "jalr $10"<<endl;
        pop(31);
    }else if(rule == "statement lvalue BECOMES expr SEMI"){
        string s = n->child.front()->tokenlist.front();
        int offset = symTab[procname][s].first;
        cout << ";going to change "<<s<<" with offset "<<offset<<endl;
        gen(n->child.at(1));//get value of rval
        cout << "sw $3, -"<<offset*4<<"($29) ; save val into"<< ";set "<<s<<" with offset "<<offset<<endl;
    }else if(rule == "lvalue ID"){//return val
        string s = n->tokenlist.front();
        int offset = symTab[procname][s].first;
        cout << "lis $3" << ";get in addr of id "<<s<<" is "<<offset<<endl;
        cout << "lw $3, -"<<offset*4<<"($29) ;load val to $3"<<endl;
    }else if(rule == "lvalue LPAREN lvalue RPAREN"){//return val
        gen(n->child.front());
    }else if(rule == "dcls dcls dcl BECOMES NUM SEMI"){/////////
        gen(n->child.front());
        //dcls
        gen(n->child.at(1));
        //dcl
        currInd++;
        string tp1 = n->child.at(1)->tp;
        cout << ";save in addr of id "<<n->child.at(1)->tokenlist.back()<<" is "<<currInd<<endl;
        symTab[procname].insert(pair<string, pair<int,string> >(n->child.at(1)->tokenlist.back(), make_pair(currInd, tp1)));
        cout << "lis $8"<<endl;
        cout << ".word "<<n->tokenlist.at(1)<<endl;
        cout << "sw $8, -"<<currInd*4<<"($29)"<<endl;
        cout << "sub $30, $30, $4"<<endl;
    }else if(rule == "test expr LT expr"){
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "slt $3, $6, $3"<<endl;
    }else if(rule == "test expr EQ expr"){
        gen(n->child.front());
        cout << "add $12,$3,$0"<<endl;
        gen(n->child.at(1));
        cout << "slt $13,$3,$12"<<endl;
        cout << "slt $7,$12,$3"<<endl;
        cout << "add $3, $13, $7"<<endl;//code for NE
        cout << "sub $3, $11, $3"<<endl;//negate ne->eq
    }else if(rule == "test expr NE expr"){
        gen(n->child.front());
        cout << "add $12,$3,$0"<<endl;
        gen(n->child.at(1));
        cout << "slt $13,$3,$12"<<endl;
        cout << "slt $7,$12,$3"<<endl;
        cout << "add $3, $13, $7"<<endl;
    }else if(rule == "test expr LE expr"){
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "slt $3, $3, $6"<<endl;//code for GT
        cout << "sub $3, $11,$3"<<endl;//negate gt->le
    }else if(rule == "test expr GE expr"){
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "slt $3, $6, $3"<<endl;//code for LT
        cout << "sub $3, $11,$3"<<endl;//negate lt->ge
    }else if(rule == "test expr GT expr"){
        gen(n->child.front());
        push(3);
        gen(n->child.at(1));
        pop(6);
        cout << "slt $3, $3, $6"<<endl;
    }else if(rule == "statement WHILE LPAREN test RPAREN LBRACE statements RBRACE"){
        looptime++;
        int num = looptime;
        cout <<"; ("<<endl;
        cout << "loop"<<num<<":"<<endl;
        gen(n->child.front());
        cout << "beq $3,$0,endloop"<<num<<endl;
        gen(n->child.back());
        cout << "beq $0, $0, loop"<<num<<endl;
        cout << "endloop"<<num<<": ; end loop"<<endl;
        cout << "; )"<< endl;
    }else if(rule == "statement IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE"){//////////////////////////////////////
        ifelsetime++;
        int num = ifelsetime;
        gen(n->child.front());
        cout << "beq $3,$0,else"<<num<<endl;
        gen(n->child.at(1));
        cout << "beq $0,$0,endif"<<num<<endl;
        cout <<"else"<<num<<": "<<endl;
        gen(n->child.at(2));
        cout <<"endif"<<num<<": "<<endl;
    }else if(rule == "factor STAR factor"){
        gen(n->child.front());
        cout <<"// $3 is an address"<<endl;
        cout << "lw $3,0($3)"<<endl;
    }else if(rule == "lvalue STAR factor"){
        
    }else if(rule == "factor NULL"){
        cout << "add $3, $0,$0"<<endl;
    }else if(rule == "type INT STAR"){
        
    }else if(rule == "dcls dcls dcl BECOMES NULL SEMI"){//////
        gen(n->child.front());
        gen(n->child.at(1));
        
    }else if(rule == " factor AMP lvalue"){
        if(n->child.back()->rule == "lvalue ID"){
            string id = n->child.back()->tokenlist.back();
            cout <<"lis $3"<<endl;
            cout <<".word -"<<symTab[procname][id].first * 4<<endl;/////////? offset be -?
            cout << "add $3, $29, $3"<<endl;
        }else if(n->child.back()->rule == "lvalue STAR factor"){
            gen(n->child.front());
        }else if(n->child.back()->rule == "lvalue LPAREN lvalue RPAREN"){
            gen(n->child.front());
        }
    }else{
        for (vector<Node* >::iterator it =  n->child.begin(); it !=  n->child.end(); ++it) {
            gen(*it);
        }
    }
}
int main(void){
    vector<string> startLine;
    Node* root = new Node(S,"",startLine);
    readIn(cin,root);
    traverse(root);
    procname = "";
    hasParam = true;
    callingParam.clear();
    //printWrapper(symMaps);
    getType(root);
    callingProcStack.clear();
    params.clear();
    
    cout << ".import print"<<endl;
    gen(root);
    symTab.clear();
    symMaps.clear();
    
    subSymTab.clear();
    callingProcStack.clear();
    clean(root);
    
    return 0;
}

