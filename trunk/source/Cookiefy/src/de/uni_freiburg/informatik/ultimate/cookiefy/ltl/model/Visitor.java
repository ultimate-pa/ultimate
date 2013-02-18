package de.uni_freiburg.informatik.ultimate.cookiefy.ltl.model;

public class Visitor {
	
	protected void visit(And f){
		visit((BinaryOperator)f);
	}
	
	protected void visit(Finally f){
		visit((UnaryOperator)f);
	}

	protected void visit(Or f) {
		visit((BinaryOperator)f);
	}

	protected void visit(Release f) {
		visit((BinaryOperator)f);
	}

	protected void visit(Until f) {
		visit((BinaryOperator)f);
	}

	protected void visit(WeakUntil f) {
		visit((BinaryOperator)f);
	}

	protected void visit(Not f) {
		visit((UnaryOperator)f);
	}

	protected void visit(Next f) {
		visit((UnaryOperator)f);
	}

	protected void visit(Globally f) {
		visit((UnaryOperator)f);
	}

	protected void visit(Literal f) {
		
	}
	
	protected void visit(BinaryOperator f){
		
	}
	
	protected void visit(UnaryOperator f){
		
	}

}
