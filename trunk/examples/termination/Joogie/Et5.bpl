type ref;
type realVar;
type classConst;
// type Field x;
// var $HeapVar : <x>[ref, Field x]x;

const unique $null : ref ;
const unique $intArrNull : [int]int ;
const unique $realArrNull : [int]realVar ;
const unique $refArrNull : [int]ref ;

const unique $arrSizeIdx : int;
var $intArrSize : [int]int;
var $realArrSize : [realVar]int;
var $refArrSize : [ref]int;

var $stringSize : [ref]int;

//built-in axioms 
axiom ($arrSizeIdx == -1);

//note: new version doesn't put helpers in the perlude anymore//Prelude finished 



var int$Random$index0 : int;
var java.lang.String$lp$$rp$$Random$args254 : [int]ref;


// procedure is generated by joogie.
function {:inline true} $neref(x : ref, y : ref) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $realarrtoref($param00 : [int]realVar) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $modreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $leref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $modint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $gtref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrealarray($param00 : [int]realVar, $param11 : [int]realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addint(x : int, y : int) returns (__ret : int) {
(x + y)
}


// procedure is generated by joogie.
function {:inline true} $subref($param00 : ref, $param11 : ref) returns (__ret : ref);



// <java.lang.Object: void <init>()>
procedure void$java.lang.Object$$la$init$ra$$28(__this : ref);



// procedure is generated by joogie.
function {:inline true} $inttoreal($param00 : int) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negReal($param00 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $ushrint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $refarrtoref($param00 : [int]ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $mulref($param00 : ref, $param11 : ref) returns (__ret : ref);



// <java.lang.String: int length()>
procedure int$java.lang.String$length$59(__this : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $neint(x : int, y : int) returns (__ret : int) {
if (x != y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorefarr($param00 : ref) returns (__ret : [int]ref);



// procedure is generated by joogie.
function {:inline true} $gtint(x : int, y : int) returns (__ret : int) {
if (x > y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $reftoint($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $addref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $xorreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $cmpreal(x : realVar, y : realVar) returns (__ret : int) {
if ($ltreal((x), (y)) == 1) then 1 else if ($eqreal((x), (y)) == 1) then 0 else -1
}


// <Et5: void <init>()>
procedure void$Et5$$la$init$ra$$2228(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r01 : ref;
Block16:
	r01 := __this;
	 assert ($neref((r01), ($null))==1);
	 //  @line: 1
	 call void$java.lang.Object$$la$init$ra$$28((r01));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $addreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $gtreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqreal(x : realVar, y : realVar) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ltint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $newvariable($param00 : int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $divint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geint(x : int, y : int) returns (__ret : int) {
if (x >= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $mulint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $leint(x : int, y : int) returns (__ret : int) {
if (x <= y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $shlref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqrefarray($param00 : [int]ref, $param11 : [int]ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftointarr($param00 : ref) returns (__ret : [int]int);



// procedure is generated by joogie.
function {:inline true} $ltref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $mulreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shrref($param00 : ref, $param11 : ref) returns (__ret : int);



// <Random: void <init>()>
procedure void$Random$$la$init$ra$$2230(__this : ref)  requires ($neref((__this), ($null))==1);
 {
var r022 : ref;
Block27:
	r022 := __this;
	 assert ($neref((r022), ($null))==1);
	 //  @line: 1
	 call void$java.lang.Object$$la$init$ra$$28((r022));
	 return;
}


// procedure is generated by joogie.
function {:inline true} $ushrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shrreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $divreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $orint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $reftorealarr($param00 : ref) returns (__ret : [int]realVar);



// procedure is generated by joogie.
function {:inline true} $cmpref(x : ref, y : ref) returns (__ret : int) {
if ($ltref((x), (y)) == 1) then 1 else if ($eqref((x), (y)) == 1) then 0 else -1
}


// procedure is generated by joogie.
function {:inline true} $realtoint($param00 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $geref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqint(x : int, y : int) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $ushrref($param00 : ref, $param11 : ref) returns (__ret : int);



	 //  @line: 5
// <Random: int random()>
procedure int$Random$random$2231() returns (__ret : int)
  modifies int$Random$index0, $stringSize;
 {
var $i226 : int;
var $i430 : int;
var $i024 : int;
var r028 : ref;
var $i329 : int;
var $r123 : [int]ref;
var $i531 : int;
var $i125 : int;
var $r227 : [int]ref;
	 //  @line: 6
Block28:
	 //  @line: 6
	$i125 := int$Random$index0;
	 //  @line: 6
	$r123 := java.lang.String$lp$$rp$$Random$args254;
	 //  @line: 6
	$i024 := $refArrSize[$r123[$arrSizeIdx]];
	 goto Block29;
	 //  @line: 6
Block29:
	 goto Block30, Block32;
	 //  @line: 6
Block30:
	 assume ($ltint(($i125), ($i024))==1);
	 goto Block31;
	 //  @line: 6
Block32:
	 //  @line: 6
	 assume ($negInt(($ltint(($i125), ($i024))))==1);
	 //  @line: 7
	__ret := 0;
	 return;
	 //  @line: 9
Block31:
	 //  @line: 9
	$r227 := java.lang.String$lp$$rp$$Random$args254;
	 goto Block33;
	 //  @line: 9
Block33:
	 //  @line: 9
	$i226 := int$Random$index0;
	 assert ($geint(($i226), (0))==1);
	 assert ($ltint(($i226), ($refArrSize[$r227[$arrSizeIdx]]))==1);
	 //  @line: 9
	r028 := $r227[$i226];
	 //  @line: 10
	$i329 := int$Random$index0;
	 //  @line: 10
	$i430 := $addint(($i329), (1));
	 //  @line: 10
	int$Random$index0 := $i430;
	$i531 := $stringSize[r028];
	 //  @line: 11
	__ret := $i531;
	 return;
}


// procedure is generated by joogie.
function {:inline true} $modref($param00 : ref, $param11 : ref) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $eqintarray($param00 : [int]int, $param11 : [int]int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negRef($param00 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $lereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $nereal(x : realVar, y : realVar) returns (__ret : int) {
if (x != y) then 1 else 0
}


	 //  @line: 2
// <Random: void <clinit>()>
procedure void$Random$$la$clinit$ra$$2232()
  modifies int$Random$index0;
 {
	 //  @line: 3
Block34:
	 //  @line: 3
	int$Random$index0 := 0;
	 return;
}


// procedure is generated by joogie.
function {:inline true} $instanceof($param00 : ref, $param11 : classConst) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $orref($param00 : ref, $param11 : ref) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $intarrtoref($param00 : [int]int) returns (__ret : ref);



// procedure is generated by joogie.
function {:inline true} $subreal($param00 : realVar, $param11 : realVar) returns (__ret : realVar);



// procedure is generated by joogie.
function {:inline true} $shlreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $negInt(x : int) returns (__ret : int) {
if (x == 0) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $gereal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $eqref(x : ref, y : ref) returns (__ret : int) {
if (x == y) then 1 else 0
}


// procedure is generated by joogie.
function {:inline true} $cmpint(x : int, y : int) returns (__ret : int) {
if (x < y) then 1 else if (x == y) then 0 else -1
}


	 //  @line: 2
// <Et5: void main(java.lang.String[])>
procedure void$Et5$main$2229($param_0 : [int]ref)
  modifies $stringSize, java.lang.String$lp$$rp$$Random$args254;
 {
var i010 : int;
var i112 : int;
var i920 : int;
var $i516 : int;
var $i213 : int;
var $i617 : int;
var r02 : [int]ref;
var i1021 : int;
var $i415 : int;
var i819 : int;
var $i314 : int;
var $i718 : int;
Block17:
	r02 := $param_0;
	 //  @line: 3
	java.lang.String$lp$$rp$$Random$args254 := r02;
	 //  @line: 4
	 call i819 := int$Random$random$2231();
	 //  @line: 5
	 call i920 := int$Random$random$2231();
	 //  @line: 6
	 call i1021 := int$Random$random$2231();
	 goto Block18;
	 //  @line: 7
Block18:
	 goto Block21, Block19;
	 //  @line: 7
Block21:
	 //  @line: 7
	 assume ($negInt(($ltint((i1021), (0))))==1);
	 //  @line: 8
	 call i010 := int$Random$random$2231();
	 //  @line: 9
	 call i112 := int$Random$random$2231();
	 //  @line: 10
	$i213 := $mulint((2), (i819));
	 //  @line: 10
	$i516 := $subint(($i213), (i920));
	 //  @line: 10
	$i314 := $mulint((2), (i010));
	 //  @line: 10
	$i415 := $subint(($i314), (i112));
	 goto Block22;
	 //  @line: 7
Block19:
	 assume ($ltint((i1021), (0))==1);
	 goto Block20;
	 //  @line: 10
Block22:
	 goto Block23, Block25;
	 //  @line: 15
Block20:
	 return;
	 //  @line: 10
Block23:
	 assume ($gtint(($i516), ($i415))==1);
	 goto Block24;
	 //  @line: 10
Block25:
	 //  @line: 10
	 assume ($negInt(($gtint(($i516), ($i415))))==1);
	 goto Block20;
	 //  @line: 11
Block24:
	 //  @line: 11
	i819 := i010;
	 goto Block26;
	 //  @line: 12
Block26:
	 //  @line: 12
	i920 := i112;
	 //  @line: 13
	$i617 := $mulint((2), (i819));
	 //  @line: 13
	$i718 := $addint((i1021), ($i617));
	 //  @line: 13
	i1021 := $subint(($i718), (i920));
	 goto Block18;
}


// procedure is generated by joogie.
function {:inline true} $andint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $andreal($param00 : realVar, $param11 : realVar) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $shlint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $xorint($param00 : int, $param11 : int) returns (__ret : int);



// procedure is generated by joogie.
function {:inline true} $subint(x : int, y : int) returns (__ret : int) {
(x - y)
}


