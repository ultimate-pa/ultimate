package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class InterferencePrecisionRegressionTest {

	private static final String MAIN_THREAD_ID = "main";
	private static final String INTERFERING_THREAD_ID = "writer";
	private static final String OBSERVER_THREAD_ID = "observer";
	private static final IProgressAwareTimer ALWAYS_RUNNING_TIMER = new IProgressAwareTimer() {
		@Override
		public boolean continueProcessing() {
			return true;
		}

		@Override
		public IProgressAwareTimer getChildTimer(final long timeout) {
			return this;
		}

		@Override
		public IProgressAwareTimer getChildTimer(final double percentage) {
			return this;
		}

		@Override
		public IProgressAwareTimer getTimer(final long timeout) {
			return this;
		}

		@Override
		public IProgressAwareTimer getParent() {
			return null;
		}

		@Override
		public long getDeadline() {
			return -1;
		}

		@Override
		public long remainingTime() {
			return Long.MAX_VALUE;
		}
	};

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mManagedScript;
	private DefaultIcfgSymbolTable mBaseSymbolTable;
	private Sort mIntSort;

	private ProgramNonOldVar mW;
	private ProgramNonOldVar mRaceX;
	private ProgramNonOldVar mLocWriter;

	private PrimedDefaultIcfgSymbolTable mPrimedSymbolTable;
	private BasicPredicateFactory mPredicateFactory;
	private RelationalPredicatePostcondition mRelationalPost;
	private IntervalDomain mIntervalDomain;
	private SymbolicTools mTools;
	private SifaStats mStats;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mManagedScript = new ManagedScript(mServices, mScript);
		mManagedScript.lock(this);
		mBaseSymbolTable = new DefaultIcfgSymbolTable();
		mIntSort = mScript.sort("Int");
	}

	@After
	public void tearDown() {
		mManagedScript.unlock(this);
		mScript.exit();
	}

	@Test
	public void postOnlyKeepsRaceValueInsideMutex() {
		initializeAnalysis();

		final IPredicate state = predicate(
				and(eq(varTv(mW), num(1)), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(1))));
		final IPredicate writeCriticalSection = writerWriteRaceZero();

		mManagedScript.unlock(this);
		final IPredicate post = mRelationalPost.strongestPostcondition(state, writeCriticalSection);
		mManagedScript.lock(this);

		assertUnsat(and(post.getFormula(), eq(varTv(mRaceX), num(1))));
		assertSat(and(post.getFormula(), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(2))));
	}

	@Test
	public void interferenceFixpointJoinWorks() {
		initializeAnalysis();

		final IPredicate state = predicate(
				and(eq(varTv(mW), num(1)), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(1))));
		final IInterferenceSet itf = mutexInterferences();

		mManagedScript.unlock(this);
		final IPredicate fixedJoin =
				itf.applyUntilFixpoint(state, OBSERVER_THREAD_ID, Set.of(INTERFERING_THREAD_ID), Set.of(),
						mIntervalDomain, 20, mStats);
		mManagedScript.lock(this);

		assertUnsat(and(fixedJoin.getFormula(), eq(varTv(mRaceX), num(1))));
		assertSat(and(fixedJoin.getFormula(), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(3))));
	}

	@Test
	public void symbolicPostThenFixpointJoinWorks() {
		initializeAnalysis();

		final IPredicate state = predicate(
				and(eq(varTv(mW), num(1)), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(1))));
		final IIcfgInternalTransition<IcfgLocation> transition = identityTransition();
		final IInterferenceSet itf = mutexInterferences();

		mManagedScript.unlock(this);
		final IPredicate post = mTools.post(state, transition);
		final IPredicate fixedJoin =
				itf.applyUntilFixpoint(post, OBSERVER_THREAD_ID, Set.of(INTERFERING_THREAD_ID), Set.of(),
						mIntervalDomain, 20, mStats);
		mManagedScript.lock(this);

		assertUnsat(and(fixedJoin.getFormula(), eq(varTv(mRaceX), num(1))));
		assertSat(and(fixedJoin.getFormula(), eq(varTv(mRaceX), num(0)), eq(varTv(mLocWriter), num(3))));
	}

	private void initializeAnalysis() {
		mW = createIntGlobal("w");
		mRaceX = createIntGlobal("race_x");
		mLocWriter = createIntGlobal("v_loc_writer");

		mPrimedSymbolTable = new PrimedDefaultIcfgSymbolTable(mBaseSymbolTable, Collections.emptySet(), mManagedScript);
		mPredicateFactory = new BasicPredicateFactory(mServices, mManagedScript, mPrimedSymbolTable);
		mRelationalPost = new RelationalPredicatePostcondition(mServices, mManagedScript, mPredicateFactory,
				mPrimedSymbolTable);

		mStats = new SifaStats();
		final CfgSmtToolkit toolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(new HashRelation<>()),
				mManagedScript, mPrimedSymbolTable, Collections.emptySet(), Collections.emptyMap(),
				Collections.emptyMap(), null, null, null);
		mTools = new SymbolicTools(mServices, mStats, new MinimalIcfg(toolkit), SimplificationTechnique.NONE,
				mPrimedSymbolTable);
		final ILogger logger = mServices.getLoggingService().getLogger(getClass());
		mIntervalDomain = new IntervalDomain(logger, mTools, 8, () -> ALWAYS_RUNNING_TIMER);
	}

	private IInterferenceSet mutexInterferences() {
		final Term all = SmtUtils.orWithExtendedLocalSimplification(mScript, List.of(writerWriteRaceZero().getFormula(),
				writerUnlock().getFormula(), unreachableOtherThreadWriteOne().getFormula()));
		final IPredicate asPredicate = predicate(all);
		final var key = new InterferenceGroupKey(INTERFERING_THREAD_ID, new AbstractLocationPair(0, 0),
				Set.of(), null, Set.of());
		final var contribution = new StrongestPostconditionInterference.RelationalInterference(asPredicate,
				mRelationalPost.prepareRelation(asPredicate), asPredicate, false);
		return new StrongestPostconditionInterference(Map.of(key, contribution), Map.of(), mRelationalPost);
	}

	private IPredicate writerWriteRaceZero() {
		return predicate(and(eq(varTv(mLocWriter), num(1)), eq(primedTv(mLocWriter), num(2)), eq(varTv(mW), num(1)),
				eq(primedTv(mW), num(1)), eq(primedTv(mRaceX), num(0))));
	}

	private IPredicate writerUnlock() {
		return predicate(and(eq(varTv(mLocWriter), num(2)), eq(primedTv(mLocWriter), num(3)), eq(varTv(mW), num(1)),
				eq(primedTv(mW), num(0)), eq(primedTv(mRaceX), varTv(mRaceX))));
	}

	private IPredicate unreachableOtherThreadWriteOne() {
		return predicate(and(eq(varTv(mLocWriter), num(7)), eq(primedTv(mLocWriter), num(8)), eq(varTv(mW), num(1)),
				eq(primedTv(mW), num(1)), eq(primedTv(mRaceX), num(1))));
	}

	private IIcfgInternalTransition<IcfgLocation> identityTransition() {
		final IcfgLocation source = new IcfgLocation(new StringDebugIdentifier("src"), MAIN_THREAD_ID);
		final IcfgLocation target = new IcfgLocation(new StringDebugIdentifier("tgt"), MAIN_THREAD_ID);
		return new InternalTransitionForTest(source, target, MAIN_THREAD_ID,
				createIdentityTransformula(List.of(mW, mRaceX, mLocWriter)));
	}

	private UnmodifiableTransFormula createIdentityTransformula(final List<IProgramVar> vars) {
		final TransFormulaBuilder builder = new TransFormulaBuilder(null, null, true, null, true, null, true);
		final List<Term> conjuncts = new ArrayList<>();
		for (final IProgramVar var : vars) {
			final TermVariable in = mManagedScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_in",
					var.getTermVariable().getSort());
			final TermVariable out = mManagedScript.constructFreshTermVariable(var.getGloballyUniqueId() + "_out",
					var.getTermVariable().getSort());
			builder.addInVar(var, in);
			builder.addOutVar(var, out);
			conjuncts.add(eq(out, in));
		}
		builder.setFormula(SmtUtils.and(mScript, conjuncts));
		builder.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return builder.finishConstruction(mManagedScript);
	}

	private ProgramNonOldVar createIntGlobal(final String name) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(name, mIntSort, mManagedScript,
				this);
		mBaseSymbolTable.add(var);
		return var;
	}

	private IPredicate predicate(final Term formula) {
		return mPredicateFactory.newPredicate(formula);
	}

	private Term varTv(final IProgramVar var) {
		return var.getTermVariable();
	}

	private Term primedTv(final IProgramVar var) {
		return mPrimedSymbolTable.getPrimedVar(var);
	}

	private Term eq(final Term left, final Term right) {
		return mScript.term("=", left, right);
	}

	private Term num(final int n) {
		return mScript.numeral(Integer.toString(n));
	}

	private Term and(final Term... conjuncts) {
		return SmtUtils.and(mScript, conjuncts);
	}

	private void assertSat(final Term formula) {
		assertEquals(LBool.SAT, SmtUtils.checkSatTerm(mScript, formula));
	}

	private void assertUnsat(final Term formula) {
		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript, formula));
	}

	private static final class MinimalIcfg implements IIcfg<IcfgLocation> {
		private static final long serialVersionUID = 1L;
		private final CfgSmtToolkit mToolkit;
		private IPayload mPayload;

		private MinimalIcfg(final CfgSmtToolkit toolkit) {
			mToolkit = toolkit;
		}

		@Override
		public CfgSmtToolkit getCfgSmtToolkit() {
			return mToolkit;
		}

		@Override
		public Map<String, Map<DebugIdentifier, IcfgLocation>> getProgramPoints() {
			return Collections.emptyMap();
		}

		@Override
		public Map<String, IcfgLocation> getProcedureEntryNodes() {
			return Collections.emptyMap();
		}

		@Override
		public Map<String, IcfgLocation> getProcedureExitNodes() {
			return Collections.emptyMap();
		}

		@Override
		public Map<String, Set<IcfgLocation>> getProcedureErrorNodes() {
			return Collections.emptyMap();
		}

		@Override
		public Set<IcfgLocation> getLocationsOfInterest() {
			return Collections.emptySet();
		}

		@Override
		public Set<IcfgLocation> getLoopLocations() {
			return Collections.emptySet();
		}

		@Override
		public Set<IcfgLocation> getInitialNodes() {
			return Collections.emptySet();
		}

		@Override
		public String getIdentifier() {
			return "minimal-icfg";
		}

		@Override
		public Class<IcfgLocation> getLocationClass() {
			return IcfgLocation.class;
		}

		@Override
		public IPayload getPayload() {
			if (mPayload == null) {
				mPayload = new Payload();
			}
			return mPayload;
		}

		@Override
		public boolean hasPayload() {
			return mPayload != null;
		}
	}

	private static final class InternalTransitionForTest implements IIcfgInternalTransition<IcfgLocation> {
		private static final long serialVersionUID = 1L;
		private final IcfgLocation mSource;
		private final IcfgLocation mTarget;
		private final String mProcedure;
		private final UnmodifiableTransFormula mTransformula;
		private IPayload mPayload;

		private InternalTransitionForTest(final IcfgLocation source, final IcfgLocation target, final String procedure,
				final UnmodifiableTransFormula transformula) {
			mSource = source;
			mTarget = target;
			mProcedure = procedure;
			mTransformula = transformula;
		}

		@Override
		public IcfgLocation getSource() {
			return mSource;
		}

		@Override
		public IcfgLocation getTarget() {
			return mTarget;
		}

		@Override
		public String getPrecedingProcedure() {
			return mProcedure;
		}

		@Override
		public String getSucceedingProcedure() {
			return mProcedure;
		}

		@Override
		public UnmodifiableTransFormula getTransformula() {
			return mTransformula;
		}

		@Override
		public IPayload getPayload() {
			if (mPayload == null) {
				mPayload = new Payload();
			}
			return mPayload;
		}

		@Override
		public boolean hasPayload() {
			return mPayload != null;
		}
	}
}
