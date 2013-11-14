package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import junit.framework.TestCase;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class TermCompilerTest extends TestCase {

	private Script solver;
	private Term a,b,c,x,y,z,t,f,three,five;
	private TermCompiler compiler;
	
	public TermCompilerTest() {
		solver = new SMTInterpol(Logger.getRootLogger(), true);
		solver.setLogic(Logics.QF_LIA);
		Sort boolSort = solver.sort("Bool");
		Sort intSort = solver.sort("Int");
		Sort[] empty = {};
		solver.declareFun("a", empty, boolSort);
		solver.declareFun("b", empty, boolSort);
		solver.declareFun("c", empty, boolSort);
		solver.declareFun("x", empty, intSort);
		solver.declareFun("y", empty, intSort);
		solver.declareFun("z", empty, intSort);
		a = solver.term("a");
		b = solver.term("b");
		c = solver.term("c");
		x = solver.term("x");
		y = solver.term("y");
		z = solver.term("z");
		t = solver.term("true");
		f = solver.term("false");
		three = solver.numeral("3");
		five = solver.numeral("5");
		compiler = new TermCompiler();
		compiler.setProofTracker(new NoopProofTracker());
	}
	
	public void testNot() {
		Term nota = solver.term("not", a);
		Term res = compiler.transform(nota);
		assertSame(nota, res);
		res = compiler.transform(solver.term("not", nota));
		assertSame(a, res);
		res = compiler.transform(solver.term("not", t));
		assertSame(f, res);
		res = compiler.transform(solver.term("not", f));
		assertSame(t, res);
	}
	
	public void testOr() {
		Term res = compiler.transform(solver.term("or", a, t));
		assertSame(t, res);
		res = compiler.transform(solver.term("or", a, f, b));
		assertSame(solver.term("or", a, b), res);
		res = compiler.transform(solver.term("or", a, a));
		assertSame(a, res);
		res = compiler.transform(solver.term("or", a, b, c, a));
		assertSame(solver.term("or", a, b, c), res);
	}
	
	public void testAnd() {
		Term in = solver.term("and", a, b);
		Term ex = solver.term("not",
				solver.term("or", solver.term("not", a),
						solver.term("not", b)));
		Term res = compiler.transform(in);
		assertSame(ex, res);
		in = solver.term("and", a, a);
		res = compiler.transform(in);
		assertSame(a, res);
		in = solver.term("and", a, b, c, a);
		ex = solver.term("not",
				solver.term("or", solver.term("not", a),
						solver.term("not", b), solver.term("not", c)));
		res = compiler.transform(in);
		assertSame(ex, res);
	}
	
	public void testIte() {
		Term res = compiler.transform(solver.term("ite", t, a, b));
		assertSame(a, res);
		res = compiler.transform(solver.term("ite", f, a, b));
		assertSame(b, res);
		res = compiler.transform(solver.term("ite", c, a, a));
		assertSame(a, res);
		res = compiler.transform(solver.term("ite", c, t, f));
		assertSame(c, res);
		res = compiler.transform(solver.term("ite", c, f, t));
		assertSame(solver.term("not", c), res);
		res = compiler.transform(solver.term("ite", c, t, a));
		assertSame(solver.term("or", c, a), res);
		res = compiler.transform(solver.term("ite", c, f, a));
		assertSame(
				solver.term("not", solver.term("or", c, solver.term("not", a))),
				res);
		res = compiler.transform(solver.term("ite", c, a, t));
		assertSame(solver.term("or", solver.term("not", c), a), res);
		res = compiler.transform(solver.term("ite", c, a, f));
		assertSame(solver.term("not", 
				solver.term("or", solver.term("not", c),
						solver.term("not", a))), res);
		Term cab = solver.term("ite", c, a, b);
		res = compiler.transform(cab);
		assertSame(cab, res);
	}
	
	public void testEq() {
		Term in = solver.term("=", x, y, three, five);
		Term res = compiler.transform(in);
		assertSame(res, f);
		in = solver.term("=", x, y, x);
		res = compiler.transform(in);
		assertSame(solver.term("=", x, y), res);
		in = solver.term("=", x, x);
		res = compiler.transform(in);
		assertSame(t, res);
		in = solver.term("=", t, a, f);
		res = compiler.transform(in);
		assertSame(f, res);
		in = solver.term("=", f, a, t);
		res = compiler.transform(in);
		assertSame(f, res);
		in = solver.term("=", a, b, t);
		Term exp = solver.term("not",
				solver.term("or", solver.term("not", a),
						solver.term("not", b)));
		res = compiler.transform(in);
		assertSame(exp, res);
		in = solver.term("=", a, b, f);
		exp = solver.term("not", solver.term("or", a, b));
		res = compiler.transform(in);
		assertSame(exp, res);
		in = solver.term("=", a, b, c, a);
		exp = solver.term("not", solver.term("or",
				solver.term("not", solver.term("=", a, b)),
				solver.term("not", solver.term("=", b, c))));
		res = compiler.transform(in);
		assertSame(exp, res);
	}
	
	public void testDistinct() {
		Term in = solver.term("distinct", a, b, c);
		Term res = compiler.transform(in);
		assertSame(f, res);
		in = solver.term("distinct", a, f);
		res = compiler.transform(in);
		assertSame(a, res);
		in = solver.term("distinct", a, t);
		res = compiler.transform(in);
		assertSame(solver.term("not", a), res);
		in = solver.term("distinct", f, a);
		res = compiler.transform(in);
		assertSame(a, res);
		in = solver.term("distinct", t, a);
		res = compiler.transform(in);
		assertSame(solver.term("not", a), res);
		in = solver.term("distinct", a, a);
		res = compiler.transform(in);
		assertSame(f, res);
		in = solver.term("distinct", a, solver.term("not", a));
		res = compiler.transform(in);
		assertSame(t, res);
		in = solver.term("distinct", a, solver.term("not", b));
		res = compiler.transform(in);
		assertSame(solver.term("=", a, b), res);
		in = solver.term("distinct", solver.term("not", a), b);
		res = compiler.transform(in);
		assertSame(solver.term("=", a, b), res);
		in = solver.term("distinct", a, b);
		res = compiler.transform(in);
		assertSame(solver.term("=", a, solver.term("not", b)), res);
		in = solver.term("distinct", x, y, x);
		res = compiler.transform(in);
		assertSame(f, res);
		in = solver.term("distinct", x, y);
		res = compiler.transform(in);
		assertSame(solver.term("not", solver.term("=", x, y)), res);
		in = solver.term("distinct", x, y, z);
		res = compiler.transform(in);
		Term exp = solver.term("not", solver.term("or",
				solver.term("=", x, y), solver.term("=", x, z),
				solver.term("=", y, z)));
		assertSame(exp, res);
	}
}
