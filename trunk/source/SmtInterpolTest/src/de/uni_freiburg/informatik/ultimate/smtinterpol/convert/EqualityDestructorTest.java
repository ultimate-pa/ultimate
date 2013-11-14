package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import junit.framework.TestCase;

public class EqualityDestructorTest extends TestCase {
	private Script m_Script;
	private TermCompiler m_Compiler = new TermCompiler();
	private Sort m_Int, m_U;
	private Term m_IC1, m_IC2;
	private Term m_UC1, m_UC2;
	public EqualityDestructorTest() {
		m_Script = new SMTInterpol(Logger.getRootLogger(), true);
		m_Script.setLogic(Logics.QF_UFLIA);
		m_Int = m_Script.sort("Int");
		m_Script.declareSort("U", 0);
		m_U = m_Script.sort("U");
		m_Script.declareFun("ic1", new Sort[0], m_Int);
		m_Script.declareFun("ic2", new Sort[0], m_Int);
		m_IC1 = m_Script.term("ic1");
		m_IC2 = m_Script.term("ic2");
		m_Script.declareFun("f", new Sort[] {m_U}, m_U);
		m_Script.declareFun("uc1", new Sort[0], m_U);
		m_Script.declareFun("uc2", new Sort[0], m_U);
		m_UC1 = m_Script.term("uc1");
		m_UC2 = m_Script.term("uc2");
		m_Compiler.setProofTracker(new NoopProofTracker());
	}
	
	/**
	 * Test case for the destruction of
	 * (exists ((x::Int)) (and (= x 3) (< x 2))) to false. 
	 */
	public void testDestructToFalse() {
		Term body = m_Script.term("and",
				m_Script.term("=",
						m_Script.variable("x", m_Int), m_Script.numeral("3")),
				m_Script.term("<",
						m_Script.variable("x", m_Int), m_Script.numeral("2")));
		Term ibody = m_Compiler.transform(body);
		EqualityDestructor ed = new EqualityDestructor();
		Term dbody = ed.destruct(ibody);
		assertSame(m_Script.term("false"), dbody);
	}
	
	public void testDestructInAffineTerm() {
		Term body = m_Script.term("and",
				m_Script.term("=",
						m_Script.variable("x", m_Int), m_Script.numeral("3")),
				m_Script.term("<=",
						m_Script.term("+", 
								m_Script.variable("x", m_Int), m_IC1, m_IC2),
						m_Script.numeral("0")));
		Term ibody = m_Compiler.transform(body);
		EqualityDestructor ed = new EqualityDestructor();
		Term dbody = SMTAffineTerm.cleanup(ed.destruct(ibody));
		Term expected = m_Script.term("<=",
				m_Script.term("+", m_IC1, m_IC2, m_Script.numeral("3")),
				m_Script.numeral("0"));
		assertSame(expected, dbody);
	}
	
	public void testDestructInApplicationTerm() {
		Term body = m_Script.term("and",
				m_Script.term("=", m_Script.variable("x", m_U), m_UC1),
				m_Script.term("=",m_Script.term("f", 
						m_Script.variable("x", m_U)),
					m_UC2));
		Term ibody = m_Compiler.transform(body);
		EqualityDestructor ed = new EqualityDestructor();
		Term dbody = ed.destruct(ibody);
		Term expected = m_Script.term("=", m_Script.term("f", m_UC1), m_UC2);
		assertSame(expected, dbody);
	}
	
	public void testDestructNested() {
		Term body = m_Script.term("and",
				m_Script.term("=",m_Script.term("f", 
						m_Script.variable("x", m_U)),
					m_UC2),
				m_Script.term("and",
						m_Script.term("=", m_Script.term("f", m_UC2), m_UC2),
						m_Script.term("=", m_Script.variable("x", m_U), m_UC1))
						);
		Term ibody = m_Compiler.transform(body);
		EqualityDestructor ed = new EqualityDestructor();
		Term dbody = ed.destruct(ibody);
		Term expected = m_Script.term("not",
				m_Script.term("or",
						m_Script.term("not",
								m_Script.term("=", 
										m_Script.term("f", m_UC1), m_UC2)),
						m_Script.term("not",
								m_Script.term("=",
										m_Script.term("f", m_UC2), m_UC2))
						));
		assertSame(expected, dbody);
	}
	
	// TODO: Hiding test cases
}
