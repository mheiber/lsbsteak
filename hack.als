//------------boring things
abstract sig Class {
   methods: set Method,
   parent: lone Class
}

sig AbstractClass, ConcreteClass extends Class {}

sig MethodName {}

abstract sig Method {
  method_name: one MethodName
}

sig ConcreteMethod extends Method {
  calls: set Call,
  use_static_attribute: lone UseStaticAttribute, // new attribute
}

sig AbstractMethod extends Method {}

sig Call {
   receiver: Receiver,
   call_method_name: MethodName,
   resolves_to: Method,
}

abstract sig Type {
   supertypes: set Type,
   names_class: Class
}


abstract sig Receiver {}

one sig StaticKeyword extends Receiver {}

sig Var extends Receiver {
   var_ty: Type,
   var_points_to: one (Var + Class)
}


//-------------new things
sig AbstractName, ConcreteName extends Type {}
one sig UseStaticAttribute {}


// --------------- Boring well-formedness conditions

fact "no class is its own ancestor" {
   no c: Class | c in c.^parent
}

fact "all methods are in classes, all calls are in methods, all `MethodName`s name a method" {
  all call: Call | one m: Method | call in m.calls
  all m: Method | some c: Class | m in c.methods
  all mn: MethodName | some m: Method | m.method_name = mn
}

fact "concrete classes cannot contain abstract methods" {
  no ConcreteClass.methods & AbstractMethod
}

fact "concrete classes must have implementations for all methods" {
    ConcreteClass.methods in ConcreteMethod
}

fact "a class must have all the method names of its parent" {
   all class: Class |
    class.parent.methods.method_name
    in class.methods.method_name
}

fact "methods are only inherited from parents" {
  all disj class1, class2: Class |
  all m: class1.methods |
  m in class2.methods implies
      (class1 in class2.parent or class2 in class1.parent)
}

fact "A variable that names a class must have come (transitively) from naming a class" {
  all v: Var | one class: Class | class in v.^var_points_to
}

fact "method names are unique in a class" {
  all c: Class | all disj m1, m2: c.methods |
  disj[m1.method_name, m2.method_name]
}


// ---------------Runtime semantics

fact "dynamic method resolution" {
  all call: Call | call.resolves_to = resolve[call]
}
 

// --------------- Pre-existing, obvious type-checking

fact "typing: an abstract method cannot override a concrete method " {
    all class: Class | all m, overridden: Method |
    { m.method_name = overridden.method_name
      m in (class.methods & AbstractMethod)
      overridden in class.parent.methods
    } implies m in ConcreteMethod
}

// TODO
// fact "typing: method calls are well-typed. Example: in c.foo() (where c is a name for a class) foo must exist on that class" {
//    all call: Call | one m: Method | static_resolve[call] = m
// }

fact "typing: variable aliasing reflects subtyping" {
  // var lower: subtype = .....
  // var upper: supertype = lower
  all upper, lower: Var | lower in upper.var_points_to implies upper.var_ty in lower.var_ty.supertypes
}


// --------------- New typing rules
fact "typing: aliasing rules" {
  all t1, t2: Type |
  // all rules share the same conclusion
  t2 in t1.supertypes implies (
	rule_abstract_covariant[t1, t2]
       or rule_concrete_covariant[t1, t2]
       or rule_concrete_to_abstract[t1, t2]
       or rule_abstract_to_concrete[t1, t2]
  )
}

/*
T inherits from U
----------------------------------
AbstractName<T> <: AbstractName<U>
*/
pred rule_abstract_covariant[t1, t2: Type] {
  t1 in AbstractName and t2 in AbstractName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteName<T> <: ConcreteName<U>
*/
pred rule_concrete_covariant[t1, t2: Type] {
  t1 in ConcreteName and t2 in ConcreteName
  and inherits_from[t1, t2]
}

/*
T inherits from U
----------------------------------
ConcreteName<T> <: AbstractName<U>
*/
pred rule_concrete_to_abstract[t1, t2: Type] {
  t1 in ConcreteName and t2 in AbstractName
  and inherits_from[t1, t2]
}

/*
T inherits from U                       U is a concrete class
----------------------------------
AbstractName<T> <: ConcreteName<U>
*/
pred rule_abstract_to_concrete[t1: Type, t2: Type] {
  t1 in AbstractName and t2 in ConcreteName
  and inherits_from[t1, t2]
  // the last conjunct is important. Comment it out to see a counterexample showing unsafety
  and t2.names_class in ConcreteClass
}


fact "typing: can't call abstract methods through AbstractName" {
  all call: Call | 
    call.receiver.var_ty in AbstractName implies static_resolve[call] in ConcreteMethod
}


/*
C         C is a concrete class
-------------------------
C: ConcreteName<C>

*/
fact "C has type ConcreteName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in ConcreteName) implies
   (class in ConcreteClass and v.var_ty.names_class = class)
}

/*
A          A is an abstract class
-------------------------
A: AbstractName<A>
*/
fact "C has type ConcreteName<C> when C is a concrete class" {
   all v: Var | all class: Class |
   (v.var_points_to = class and v.var_ty in AbstractName) implies
   (class in AbstractClass and v.var_ty.names_class = class)
}


// TODO
// fact "UseStatic attribute only allowed in abstract concrete methods (for simplicity)" {
//   all m: Method |
//      m.use_static implies (containing_class[m] in AbstractClass and m in ConcreteMethod)
// }

// fact "all methods in abstract classes that use static must have the UseStatic Attribute" {
//     all m: Method | (containing_class[m] in AbstractClass and StaticKeyword in m.calls.receiver) implies m.use_static
// }


// fact "cannot call UseStatic methods through variables of type AbstractName" {
//   all call: Call | static_resolve[call].use_static and call.receiver in Var implies call.receiver.var_ty in ConcreteName
// }



// ------------- helpers

pred use_static[m: Method] {
  UseStaticAttribute in m.use_static_attribute
}

fun resolve_var[v: Var]: one Class {
    {class: Class | class in v.^var_points_to} // guaranteed to be exactly one due to fact above
}

// c.foo() where c is a name for a class resolves to method foo of c *or a sub-class of c* at runtime
fun resolve[call: Call]: Method {
    {m: Method |
       (m.method_name = call.call_method_name and m in call.receiver.resolve_var.methods) 
      or  (StaticKeyword = call.receiver and (
         let class = containing_class[call] |
         let name = containing_method[call].method_name |
         m.method_name = name and m in (class + containing_class[m].^parent).methods
      ))
   }
}

// c.foo() where c is a name for a class "statically resolves" to method foo of c
fun static_resolve[call: Call]: Method {
    {m: Method |
         (m.method_name = call.call_method_name and m in call.receiver.var_ty.names_class.methods)
     or (StaticKeyword = call.receiver and (
              m.method_name = call.call_method_name and
              m in containing_class[call].methods
          ))
  }
}


fun containing_class[m: Method]: Class {
  {
     class: Class | m in class.methods and
     no ancestor: class.^parent | m in ancestor.methods
  }
}

fun containing_class[call: Call]: Class {
   call.containing_method.containing_class
}

fun containing_method[call: Call]: Method {
   {m: Method | call in m.calls }
}

pred inherits_from[descendent: Type, ancestor: Type] {
   ancestor.names_class in (descendent.names_class + descendent.names_class.^parent)
}


// ------------- pretty

fact "non-essential eta rule for AbstractName that makes visualizations easier to read" {
   all t1, t2: AbstractName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}


fact "non-essential eta rule for ConcreteName that makes visualizations easier to read" {
   all t1, t2: ConcreteName |
   t1.names_class = t2.names_class
   and t1.supertypes = t2.supertypes implies t2 = t1
}

// ------------predicates that can be used to show interesting examples
pred has_inherited_method {
  some m: Method | some disj c1, c2: Class | m in c1.methods and m in c2.methods
}

pred has_interesting_method_call {
  some call: Call | not (resolve[call] = static_resolve[call])
}

pred has_override {
  some m:  Method | some disj c1, c2: Class |
    { 
        c2 in c1.^parent
        m in c1.methods
        m not in c2.methods 
        m.method_name in c2.methods.method_name
    }
}
//---------------show

pred show { 
  // at least 1 method is abstract
  some am: AbstractMethod | am in univ
}

pred show_complicated {
  has_inherited_method
  has_interesting_method_call
  has_override
}

run  show for 3
run show_complicated for 4

run {
  some c: AbstractClass | some m: c.methods |
  some abs_meth: c.methods & AbstractMethod |
  some call: m.calls |
    {
      call.receiver = StaticKeyword
      call.call_method_name = abs_meth.method_name
      not m.use_static
      // call.resolve in AbstractMethod
    } 
} 
run {
  some call: Call |
      {
        call.resolve in AbstractMethod
      }
} 

// -------------check

assert safe {  no c: Call | resolve[c] in AbstractMethod }
check safe
check safe for 4
check safe for 5
