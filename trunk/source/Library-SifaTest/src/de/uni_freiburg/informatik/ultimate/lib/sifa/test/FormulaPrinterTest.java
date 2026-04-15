package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtManager;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.StatsWrapperDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class FormulaPrinterTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private DefaultIcfgSymbolTable mSymbolTable;
	private Sort mIntSort;
	private BasicPredicateFactory mPredicateFactory;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mMgdScript = new ManagedScript(mServices, mScript);
		mMgdScript.lock(this);
		mSymbolTable = new DefaultIcfgSymbolTable();
		mIntSort = mScript.sort("Int");
		mPredicateFactory = new BasicPredicateFactory(mServices, mMgdScript, mSymbolTable);
	}

	@After
	public void tearDown() {
		mMgdScript.unlock(this);
		mScript.exit();
	}

	@Test
	public void printFormulas() {
		ProgramNonOldVar xVar = createGlobalIntVar("x");
		ProgramNonOldVar yVar = createGlobalIntVar("y");
		TermVariable x = xVar.getTermVariable();
		TermVariable y = yVar.getTermVariable();

		// basic formulas
		// start1: x = 5 AND y = 10
		Term startTerm1 = mScript.term("and", mScript.term("=", x, mScript.numeral("5")), mScript.term("=", y, mScript.numeral("10")));
		IPredicate startPred1 = mPredicateFactory.newPredicate(startTerm1);
		
		// start2: x = 10 AND y = 5
		Term startTerm2 = mScript.term("and", mScript.term("=", x, mScript.numeral("10")), mScript.term("=", y, mScript.numeral("5")));
		IPredicate startPred2 = mPredicateFactory.newPredicate(startTerm2);

		// start3: x >= 0 AND x <= 5
		Term startTerm3 = mScript.term("and", mScript.term(">=", x, mScript.numeral("0")), mScript.term("<=", x, mScript.numeral("5")));
		IPredicate startPred3 = mPredicateFactory.newPredicate(startTerm3);

		// start4: Disjunction (OR) -> x = 0 OR x = 10
		Term startTerm4 = mScript.term("or", mScript.term("=", x, mScript.numeral("0")), mScript.term("=", x, mScript.numeral("10")));
		IPredicate startPred4 = mPredicateFactory.newPredicate(startTerm4);

		// start5: Variable alias/equivalence -> x = y
		Term startTerm5 = mScript.term("=", x, y);
		IPredicate startPred5 = mPredicateFactory.newPredicate(startTerm5);

		// start6: Pure Inequality -> x > 5 AND y < 0
		Term startTerm6 = mScript.term("and", mScript.term(">", x, mScript.numeral("5")), mScript.term("<", y, mScript.numeral("0")));
		IPredicate startPred6 = mPredicateFactory.newPredicate(startTerm6);

		System.out.println("============== FORMULA PRINTS ==============");

		IDomain[] domains = new IDomain[] {
				new ExplicitValueDomain(mServices, mMgdScript, mSymbolTable),
				new IntervalDomain(mServices, mMgdScript, mSymbolTable),
				new OctagonDomain(mServices, mMgdScript, mSymbolTable),
				new CompoundDomain(mServices, mMgdScript, mSymbolTable)
		};

		String[] domainNames = new String[] {"ExplicitValue", "Interval", "Octagon", "Compound"};

		for (int i = 0; i < domains.length; i++) {
			IDomain d = domains[i];
			String name = domainNames[i];
			
			System.out.println("\n--- Domain: " + name + " ---");
			
			// 1. startingformula
			IPredicate startF = name.equals("Interval") ? startPred3 : startPred1;
			IPredicate joinF = name.equals("Interval") ? startPred1 : startPred2;
			System.out.println("1. Starting formula:");
			System.out.println(startF.getFormula().toStringDirect());
			
			// 2. after alpha()
			IPredicate alphaF = d.alpha(startF);
			System.out.println("2. After alpha():");
			System.out.println(alphaF.getFormula().toStringDirect());
			
			// 3. after join() with some other basic formula
			IPredicate alphaJoinTarget = d.alpha(joinF);
			IPredicate joined = d.join(alphaF, alphaJoinTarget);
			System.out.println("3. After join() with " + joinF.getFormula().toStringDirect() + " (alphaed first)");
			System.out.println(joined.getFormula().toStringDirect());
			
			// 4. after alpha() and then QE on the alpha'd version
			// Let's create an existential formula to do QE on, or use SmtManager?
			// Actually QE in Ultimate is typically part of predicate factory eliminateQuantifiers.
			// Let's create a formula with a bound variable, then do QE.
			SmtManager smtManager = new SmtManager(mServices, mMgdScript, mSymbolTable);
			Term extVar1 = mMgdScript.constructFreshTermVariable("ext1", mIntSort);
			Term alphaTermWithExt = mScript.term("and", alphaF.getFormula(), mScript.term("=", x, mScript.term("+", extVar1, mScript.numeral("1"))));
			Term existsTerm = mScript.quantifier(Script.EXISTS, new TermVariable[] {(TermVariable)extVar1}, alphaTermWithExt);
			
			System.out.println("4. Original for QE (existential quantifier):");
			System.out.println(existsTerm.toStringDirect());
			
			try {
				mMgdScript.unlock(this);
				IPredicate existsPred = mPredicateFactory.newPredicate(existsTerm);
				IPredicate qePred = smtManager.eliminateQuantifiers(existsPred);
				System.out.println("4. After QE:");
				System.out.println(qePred.getFormula().toStringDirect());
				mMgdScript.lock(this);
			} catch(Exception e) {
				System.out.println("4. QE failed: " + e.getMessage());
				mMgdScript.lock(this);
			}
		}
	}

	private ProgramNonOldVar createGlobalIntVar(final String name) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(name, mIntSort, mMgdScript, this);
		mSymbolTable.add(var);
		return var;
	}
}
