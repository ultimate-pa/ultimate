//#Safe
/*
DD 2018-11-16

Leads to type error in preprocessing. 
[ERROR L1129           TypeChecker]: C: instance [9]: Undeclared identifier ~#instance~0 in IdentifierExpression[~#instance~0,GLOBAL]
[ERROR L1129           TypeChecker]: C: foo(& instance) [9]: Wrong parameter type at index 0: CallStatement[false,[],foo,[IdentifierExpression[~#instance~0,GLOBAL]]]

[L194             ResultUtil]:   - TypeErrorResult [Line: 9]: Type Error
[L198             ResultUtil]:     Undeclared identifier ~#instance~0 in IdentifierExpression[~#instance~0,GLOBAL]
[L194             ResultUtil]:   - TypeErrorResult [Line: 9]: Type Error
[L198             ResultUtil]:     Wrong parameter type at index 0: CallStatement[false,[],foo,[IdentifierExpression[~#instance~0,GLOBAL]]]
*/

struct anon_struct;

extern struct anon_struct instance ;

extern void foo(struct anon_struct *);

int main(){
    int x;
    foo(& instance);
    return 0;
}