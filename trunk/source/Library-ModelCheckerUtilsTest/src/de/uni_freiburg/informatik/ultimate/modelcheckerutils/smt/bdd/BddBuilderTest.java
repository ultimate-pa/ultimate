package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd;

import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDFactory;

public class BddBuilderTest {

	IUltimateServiceProvider services;
	Script script;
	SimplifyBdd simplifyBdd;
	Sort bool;

	@Before
	public void setUp() {
		services = UltimateMocks.createUltimateServiceProviderMock();
		script = new SMTInterpol();
		final ManagedScript mgdScript = new ManagedScript(services, script);
		simplifyBdd = new SimplifyBdd(services, mgdScript);

		script.setLogic(Logics.CORE);
		bool = ((SMTInterpol) script).getTheory().getBooleanSort();
	}

	@Test
	public void testAnd() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term t = SmtUtils.and(script, Arrays.asList(x1, x2));
		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		final BddBuilder bb = new BddBuilder();
		final BDD d = bb.buildBDD(t, atoms);

		final BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).and(factory.ithVar(1)), d);
	}

	@Test
	public void testOR() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term t = SmtUtils.or(script, Arrays.asList(x1, x2));
		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		final BddBuilder bb = new BddBuilder();
		final BDD d = bb.buildBDD(t, atoms);

		final BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).or(factory.ithVar(1)), d);
	}

	@Test
	public void testNot() {
		final Term x1 = script.variable("x1", bool);
		final Term t = SmtUtils.not(script, x1);
		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		final BddBuilder bb = new BddBuilder();
		final BDD d = bb.buildBDD(t, atoms);

		final BDDFactory factory = BDDFactory.init("java", atoms.size() + 2, atoms.size() + 2, false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).not(), d);
	}

	@Test
	public void testImp() {
		final Term x1 = script.variable("x1", bool);
		final Term x2 = script.variable("x2", bool);
		final Term t = script.term("=>", x1, x2);
		final CollectAtoms ca = new CollectAtoms();
		final List<Term> atoms = ca.getTerms(t);
		final BddBuilder bb = new BddBuilder();
		final BDD d = bb.buildBDD(t, atoms);

		final BDDFactory factory = BDDFactory.init("java", atoms.size(), atoms.size(), false);
		factory.setVarNum(atoms.size());
		Assert.assertEquals(factory.ithVar(0).imp(factory.ithVar(1)), d);
	}

}
