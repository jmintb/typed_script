# [Lang Name]

[Lang Name] is an exploratory programming language which will eventually turn into a  programming language forefilling the following properties. 

### Goals

#### Low cognitive overhead

#### Built in verification

#### Heterogenius computing with MLIR

#### Zero cost abstractions 

#### Ergonomic and expressive type system

#### Viable for "scripting" use cases

#### Blazingly fast compile times

#### Uncolored async features

#### Comptime + macros

#### Zero overhead and ergonomic automatic memory management (mutable value semantics or something else)

#### First class "unsafe" mode

#### Easy interopt with just about any language/ecosystem (except C++ haha)

#### Safety on all fronts (memory, allocation, integer overflow etc)

#### Dependent types

#### "auto" optimising for hardware similar to mojo

#### Mojo claims to expose MLIR primitives, can we do the same?

#### Mutable value semantics

### Process

How will we go about this? There are a lot of conflicting and unproven features. The first phase will be focused on proven the value of each feature as well as 
the synergy of each feature in a single language. It may well turn out that some of the features are not feasible or do not function well together. To gauge
this in a time effecient manner we will do the following. 

1. Build a very basic language as a test bed. We will use Rust's syntax as I like it but it could be any syntax in principle we just want something well proven as we are
not looking to reinvent the wheel(yet :) ). We we will stick to a very minimal subset of Rust probably just functions, structs, enums and basic data types. This should be
fast to implement as long as we aren't trying to optimize and perfect everything. There will be no memory managment, meta programing, generics or other invovled aspects at
this stage. We want the simplest possible test bed and it is important to not overengineer anything at this stage.

2. The second step will invovle implemeting each desired feature one at time and testing them. It is important to do this in a feasible manner. If well proven existing 
implementations work we will simply "copy" the existing approach as we want a minimal working feature as fast as possible. If not we will have to come up with an
approach but still try to keep things minimal. We also must keep in mind the order of feature implementation, as we also want to test the synergy of the features. Some
features will require other features so it should be possible to figure out a "correct" ordering of implementation. We want to aim for implementing and testing one feature
a month.

3. Once we are done implementing features in our test bench we will port existing large code bases to it. It is important to select projects from different domains that
pressure programming languages in different. For examples games often have global state which borrow checker style memory management can have trouble with, therefore if
we are using a borrowchecker we want to implement a game to see how our language handles that case.

4. At this point we should have a established the feasiblity and desirability of each feature. Now we will start from scratch and reimplement the language but properly.
One note here is that we will keep the compiler it self as minimal as possible. Gaps in the language should first be addressed in third party user space code using comptime + metaprogramming. Once an idea proves usefel we can move it into the std library and then the compiler for special cases. Similar to rust but avoiding
that the ecosystem becomes depedent on single deps.