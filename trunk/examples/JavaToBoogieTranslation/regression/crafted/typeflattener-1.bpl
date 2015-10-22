type ref;
type javaType;

type Field x;
type MultiField x y;

//type SynonymField = MultiField int int;

type $heap_type = <x>[ref,Field x]x;
type $heap_mtype = <x,y>[ref,MultiField x y]x;
const unique $type : Field javaType;
const unique $mtype : MultiField int ref;
const unique $null : ref;

var $heap : $heap_type;
var $mheap : $heap_mtype;
var intField : Field int;
var realField : Field real;
var Z : MultiField int ref;


procedure foo($this : ref) returns ();
modifies $heap, $mheap;

implementation foo($this : ref) returns (){
    var r01 : ref;
    var $i04 : int;
	var $i05 : real;
    var $readh : int;
    var $readhm : int;
	r01 := $this;
	havoc $i04;
	havoc $i05;
	$heap := $heap[r01,intField := $i04];
	$heap := $heap[r01,realField := $i05];
	$mheap := $mheap[r01,Z := $i04];
	$readh := $heap[r01,intField];
	$readhm := $mheap[r01,Z];
    assume $this != $null;
	return;
}
