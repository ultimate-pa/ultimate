package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateServiceProviderMock;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;


public class BddBuilderTest {
	
	IUltimateServiceProvider services;
	Script script;
	SimplifyBdd simplifyBdd;
	Sort bool;
	
	@Before
	public void setUP(){
		services = new UltimateServiceProviderMock();
		script = new SMTInterpol();
		final IFreshTermVariableConstructor freshTermVariableConstructor = null;
		simplifyBdd = new SimplifyBdd(services, script, freshTermVariableConstructor);

		script.setLogic(Logics.CORE);
		bool = ((SMTInterpol)script).getTheory().getBooleanSort();
	}
	
	@Test
	public void testAnd(){
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term t = SmtUtils.and(script, Arrays.asList(x1, x2));
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(t);
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(t, atoms);
		
		BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).and(factory.ithVar(1)), d);
	}
	
	@Test
	public void testOR(){
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term t = SmtUtils.or(script, Arrays.asList(x1, x2));
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(t);
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(t, atoms);
		
		BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).or(factory.ithVar(1)), d);
	}
	
	@Test
	public void testImp(){
		Term x1 = script.variable("x1", bool);
		Term x2 = script.variable("x2", bool);
		Term t = script.term("=>", x1, x2);
		CollectAtoms ca = new CollectAtoms();
		List<Term> atoms = ca.getTerms(t);
		BddBuilder bb = new BddBuilder();
		BDD d = bb.buildBDD(t, atoms);
		
		BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).imp(factory.ithVar(1)), d);
	}
	
}
