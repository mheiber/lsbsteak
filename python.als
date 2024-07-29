abstract sig Class {
   methods: set Method,
   parent: lone Class
}

sig AbstractClass extends Class {}

sig ConcreteClass extends Class {}
{
  no m: AbstractMethod | m in methods
}

sig MethodName {}


abstract sig Method {
  method_name: one MethodName
}
sig ConcreteMethod extends Method {
  calls: set Call
}
sig AbstractMethod extends Method {}

sig Call {
   receiver: Var,
   call_method_name: MethodName,
   resolves_to: Method
} {
   resolves_to = resolve[this]
}

sig ClassName {
   upcast: set ClassName,
   names_class: Class
}
sig AbstractName extends ClassName {}
sig ConcreteName extends ClassName {}

sig Var {
   var_ty: ClassName,
   var_val: Class
}



// --------------- Boring rules for well-formed classes

fact "no class is its own ancestor" {
   all c: Class | c not in c.^parent
}

fact "all methods are in classes, all calls are in methods, all `MethodName`s are used" {
  all m: Method | some c: Class | m in c.methods
  all call: Call | some m: Method | call in m.calls
  all mn: MethodName | some m: Method | m.method_name = mn
}

// fact "all calls are resolved" { all call: Call | one m: Method | resolve[call] = m}
fact "method names are unique in a class" {
  all c: Class | all m1: Method | all m2: Method |
  m1 in c.methods and m1.method_name = m2.method_name implies m1 = m2 
}


// --------------- Pre-existing, obvious typing rules

fact "typing: an abstract method cannot override a concrete method " {
    all m1: Method | all overridden: Method | all c: Class |
    m1 in c.methods
    and m1.method_name = overridden.method_name
    and overridden in c.^parent.methods
    and overridden in ConcreteMethod
    implies m1 in ConcreteMethod
}

fact "typing: method must be statically visible: in c.foo() (where c is a name for a class) foo must exist on that class" {
   all call: Call | some m: Method | static_resolve[call] = m
}

// --------------- helpers
pred descendent_of[n1: ClassName, n2: ClassName] {
   n2.names_class in (n1.names_class + n1.names_class.^parent)
}

// --------------- New typing rules
fact "typing: AbstractName is covariant" {
  all n1: AbstractName |
  all n2: AbstractName |
  n2 in n1.upcast  implies descendent_of[n1, n2]
}

fact "typing: ConcreteName is covariant" {
  all n1: ConcreteName |
  all n2: ConcreteName |
  n2 in n1.upcast implies descendent_of[n1, n2]
}

fact "typing: ConcreteName to AbstractName" {
  all n1: ConcreteName |
  all n2: AbstractName |
  n2 in n1.upcast  implies descendent_of[n1, n2]
}
//
//fact "typing: AbstractName to ConcreteName" { // TODO! reinstate this rule
//  all n1: AbstractName |
//  all n2: ConcreteName |
//  n2 in n1.upcast implies descendent_of[n1, n2] and n2.names_class in ConcreteClass
//}
//



fact "typing: can't call abstract methods through AbstractName" {
  all call: Call |       all m: Method |
    (call.receiver.var_ty in AbstractName and
            m.method_name = call.call_method_name and m in  static_resolve[call])
            implies m in ConcreteMethod
}

// ------------- Helpers: method resolution

// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.var_val.methods}
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c
fun static_resolve[call: Call]: Method {
    {m: Method | m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods}
}

//fact "make it interesting" {
//  some n1: AbstractName |
//  some n2: ConcreteName |
//  some call: Call |
//  n2 in n1.upcast and descendent_of[n1, n2]
//  and call.receiver.var_ty in ConcreteName and call.receiver.var_val in AbstractClass
//}


// ------------- stuff

fact "non-essential eta rule for AbstractName that makes visualizations easier to read" {
   all an: AbstractName | all an2: AbstractName |
   an2.names_class = an.names_class implies an = an2
}

// -------------run it
//run show {some m: AbstractMethod | m in AbstractMethod and some call: Call | call in Call }
assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe




