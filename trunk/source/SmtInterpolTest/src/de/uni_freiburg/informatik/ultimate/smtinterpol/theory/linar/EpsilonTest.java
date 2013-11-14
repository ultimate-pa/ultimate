package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigDecimal;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TestCaseWithLogger;

/**
 * This test case is designed to test a bug in the selection of possible values
 * for the infinitesimal parameter epsilon.  It is designed as a system test and
 * does not directly test the implementation, i.e., the concrete values computed
 * by SMTInterpol.  Instead, it checks that the model satisfies the given
 * formula using SMTInterpols model-check-mode
 * @author Juergen Christ
 */
public class EpsilonTest extends TestCaseWithLogger {

	private SMTInterpol m_Solver;
	private Term m_InputBase;
	
	private final static Sort[] EMPTY_SORT_ARRAY = {};
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		m_Solver = new SMTInterpol(Logger.getRootLogger(), false);
		m_Solver.setOption(":produce-models", Boolean.TRUE);
		m_Solver.setLogic(Logics.QF_LRA);
		Sort real = m_Solver.sort("Real");
		m_Solver.declareFun("x", EMPTY_SORT_ARRAY, real);
		m_Solver.declareFun("y", EMPTY_SORT_ARRAY, real);
		Term zero = m_Solver.decimal(BigDecimal.ZERO);
		Term one = m_Solver.decimal(BigDecimal.ONE);
		Term threeovertwo = m_Solver.decimal(BigDecimal.valueOf(3).divide(
				BigDecimal.valueOf(2)));
		Term x = m_Solver.term("x");
		Term y = m_Solver.term("y");
		m_InputBase = m_Solver.term("and",
				m_Solver.term("<=", m_Solver.term("+", x, y), one),
				m_Solver.term("<", x, zero),
				m_Solver.term("<=", y, threeovertwo));
		m_Solver.assertTerm(m_InputBase);
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		m_InputBase = null;
		m_Solver.exit();
		m_Solver = null;
	}
	
	public void testEmptyProhibitions() {
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(new Term[] {m_InputBase});
		assertEquals(1, eval.size());
		assertSame(m_Solver.term("true"), eval.get(m_InputBase));
	}
	
	public void testProhibMiss() {
		Term second = m_Solver.term("not", 
				m_Solver.term("=", 
						m_Solver.term("x"),
						m_Solver.decimal(BigDecimal.ONE)));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
	
	public void testProhibHit() {
		Term second = m_Solver.term("not", 
				m_Solver.term("=", 
						m_Solver.term("+", 
								m_Solver.term("x"), m_Solver.term("y")),
						m_Solver.decimal(BigDecimal.ONE.negate())));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
	
	public void testProhibHitLower() {
		Term second = m_Solver.term("and", m_Solver.term("not", 
				m_Solver.term("=", 
						m_Solver.term("+", 
								m_Solver.term("x"), m_Solver.term("y")),
						m_Solver.decimal(BigDecimal.ONE.negate()))),
				m_Solver.term("not", m_Solver.term("=", 
						m_Solver.term("x"),
						m_Solver.decimal(BigDecimal.ONE.negate().divide(
								BigDecimal.valueOf(2))))));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
	
	public void testProhibHitUpper() {
		Term second = m_Solver.term("and", m_Solver.term("not", 
				m_Solver.term("=", 
						m_Solver.term("+", 
								m_Solver.term("x"), m_Solver.term("y")),
						m_Solver.decimal(BigDecimal.ONE.negate()))),
				m_Solver.term("not", m_Solver.term("=", 
						m_Solver.term("x"),
						m_Solver.decimal(BigDecimal.valueOf(-2)))));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
	
	public void testProhibHitNegative() {
		Term second = m_Solver.term("and", m_Solver.term("not", 
				m_Solver.term("=", 
						m_Solver.term("+", 
								m_Solver.term("x"), m_Solver.term("y")),
						m_Solver.decimal(BigDecimal.ONE.negate()))),
				m_Solver.term("not", m_Solver.term("=", 
						m_Solver.term("x"),
						m_Solver.decimal(BigDecimal.ONE))));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
	
	public void testIntervalUpperBound() {
		Term second = m_Solver.term(">",
				m_Solver.term("y"), m_Solver.decimal(BigDecimal.ONE));
		m_Solver.assertTerm(second);
		LBool isSat = m_Solver.checkSat();
		assertSame(LBool.SAT, isSat);
		Map<Term, Term> eval = m_Solver.getValue(
				new Term[] {m_InputBase, second});
		assertEquals(2, eval.size());
		Term trueTerm = m_Solver.term("true");
		assertSame(trueTerm, eval.get(m_InputBase));
		assertSame(trueTerm, eval.get(second));
	}
}
