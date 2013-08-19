open Formula

let print_number channel (number:Z.t) =
  (if (number >= Z.zero) then
  begin
    output_string channel (Z.to_string number)
  end
  else
  begin
    output_string channel "(- ";
    output_string channel (Z.to_string (Z.abs number));
    output_string channel ")"
  end);;

let print_formula (print_atomic : out_channel -> 'atomic -> unit)
    (print_variable : out_channel -> 'variable -> unit)
    (channel : out_channel) :
    ('variable, 'atomic) quantified_formula -> unit =
  let outs = output_string channel in
  let outvl = function
    | [] -> outs ""
    | [v] -> print_variable channel v
    | h::t -> print_variable channel h;
        List.iter (fun v -> outs ", "; print_variable channel v) t in
  let rec prf : ('variable, 'atomic) quantified_formula -> unit = function
    | `And [] -> outs "true"
    | `And l -> outs "(and ";
      print_list l;
      outs ")"
    | `Or [] -> outs "false"
    | `Or l -> outs "(or ";
	print_list l;
	outs ")"
    | `Xor l -> outs "(xor ";
	print_list l;
	outs ")"
    | `Not w -> outs "(not ";
	prf w;
	outs ")"
    | `Ite(c, f1, f2) -> outs "(ite ";
	prf c;
	outs " ";
	prf f1;
	outs " ";
	prf f2;
	outs ")"
    | `Atomic a -> print_atomic channel a
    | `Exists([v], f) -> outs "(exists ((";
	outs v;
	outs " Real)) ";
	prf f;
	outs ")"
    | `Forall([v], f) -> outs "(forall ((";
	outs v;
	outs " Real)) ";
	prf f;
	outs ")"
    | `Exists(vl, f) -> outs "(exists (";
	outvl vl;
	outs ") ";
	prf f;
	outs ")"
    | `Forall(vl, f) -> outs "(forall (";
	outvl vl;
	outs ") ";
	prf f;
	outs ")"
  and print_list : ('variable, 'atomic) quantified_formula list -> unit= function
  | [] -> ()
  | [h] -> prf h
  | h::t -> prf h; outs " "; print_list t

  in prf;;

let rec print_source_expression (channel : out_channel) : source_expression -> unit = function
  | `Sum [] -> output_string channel "0"
  | `Product [] -> output_string channel "1"
  | `Sum(l) ->
      output_string channel "(+ ";
      print_source_expression_list " " channel l;
      output_string channel ")"
  | `Product(l) ->
      output_string channel "(* ";
      print_source_expression_list " " channel l;
      output_string channel ")"
  | `Quotient(x, y) ->
      output_string channel "(/ ";
      print_source_expression channel x;
      output_string channel " ";
      print_source_expression channel y;
      output_string channel ")"
  | `Neg(x) -> output_string channel "(- ";
      print_source_expression channel x;
      output_string channel ")"
  | `Integer(x) -> print_number channel x
  | `Variable(x) -> output_string channel x

and print_source_expression_list (separator : string) (channel : out_channel) : source_expression list -> unit = function
  | [] -> ()
  | [h] -> print_source_expression channel h
  | h::t -> print_source_expression channel h;
     output_string channel separator;
     print_source_expression_list separator channel t;;

let print_source_atomic channel : source_atomic -> unit = function
  | `Propositional x -> output_string channel x
  | `Comparison(lhs, op, rhs) ->
    if (op == `UNEQUAL) then
        output_string channel "(not ";
    output_string channel "(";
    output_string channel
	(match op with
	   | `LESS -> "<"
	   | `GREATER -> ">"
	   | `LESS_EQ -> "<="
       | `GREATER_EQ -> ">="
       | `EQUAL -> "="
       | `UNEQUAL -> "=");
    output_string channel " ";
    print_source_expression channel lhs;
    output_string channel " ";
    print_source_expression channel rhs;
    output_string channel ")";
    if (op == `UNEQUAL) then
        output_string channel ")";
;;

let print_source_quantified_formula : out_channel -> source_quantified_formula -> unit = print_formula print_source_atomic output_string;;

let print_source_unquantified_formula (channel : out_channel) (formula : source_unquantified_formula) =
  print_source_quantified_formula channel (unquantified_to_quantified formula);;
let print_linear_expression channel var_mapper (l : linear_expression) =
  match l with
    | [] -> output_string channel "0"
    | _ ->
	output_string channel "(+ ";
	let first = ref true in
	List.iter
	  (fun (var_id, coeff) ->
	     (if not !first then output_string channel " ");
	     first := false;
	     (if var_id >= 0 then
	       (output_string channel "(* "););
	     print_number channel coeff;
	     (if var_id >= 0 then
		   (output_string channel " ";
		    output_string channel (var_mapper var_id);
		    output_string channel ")";)
		 )
	  )
	  l;
      output_string channel ")";;
	       
let print_q_linear_expression channel var_mapper (l : q_linear_expression) =
  if (Z.compare l.num Z.one != 0)
    || (Z.compare l.den Z.one != 0) then
      begin
    if (Z.compare l.den Z.one != 0) then
      (output_string channel "(/ ";);
    if (Z.compare l.num Z.one != 0) then
      (output_string channel "(* ";);
	output_string channel "(";
	print_linear_expression channel var_mapper l.expr;
	output_string channel ")";
	(if (Z.compare l.num Z.one) != 0 then
	   begin
	     output_string channel " ";
	     print_number channel l.num;
	     output_string channel ")"
	   end);
	(if (Z.compare l.den Z.one) != 0 then
	   begin
	     output_string channel " ";
	     print_number channel l.den;
	     output_string channel ")"
	   end)
      end
  else
    print_linear_expression channel var_mapper l.expr;;

let print_linear_atomic var_mapper channel : linear_atomic -> unit = function
  | `Greater_eq expr -> 
      output_string channel "(>= ";
	  print_linear_expression channel var_mapper expr;
      output_string channel " 0)"
  | `Propositional x -> output_string channel x;;

let print_linear_quantified_formula (var_mapper : int->string) :
  out_channel -> linear_quantified_formula -> unit =
  print_formula (print_linear_atomic var_mapper) output_string;;

let print_linear_unquantified_formula var_mapper channel
    (formula : linear_unquantified_formula) =
  print_linear_quantified_formula var_mapper channel
    (unquantified_to_quantified formula);;

let print_processed_formula (channel : out_channel) (ct : linearization_context) (f : linear_unquantified_formula) =
  print_linear_unquantified_formula
    (var_mapper_of_linearization_context ct) channel f;;

Multiple_choices.add_choice output_syntax "smtlib" 20 print_source_quantified_formula "my custom smtlib syntax";;
