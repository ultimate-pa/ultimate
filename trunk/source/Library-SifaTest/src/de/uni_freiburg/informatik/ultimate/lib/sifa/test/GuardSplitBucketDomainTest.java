package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;

import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.GuardSplitBucketDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.GuardSplitBucketDomain.GuardBucketPolicy;
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

public class GuardSplitBucketDomainTest {

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
	private ProgramNonOldVar mX;
	private ProgramNonOldVar mPeerLoc;
	private SymbolicTools mTools;
	private IntervalDomain mBaseDomain;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = new SMTInterpol(new DefaultLogger());
		mScript.setLogic(Logics.ALL);
		mManagedScript = new ManagedScript(mServices, mScript);
		mManagedScript.lock(this);
		mBaseSymbolTable = new DefaultIcfgSymbolTable();
		mIntSort = mScript.sort("Int");

		mX = createIntGlobal("x");
		mPeerLoc = createIntGlobal("loc_worker2");

		final SifaStats stats = new SifaStats();
		final CfgSmtToolkit toolkit = new CfgSmtToolkit(new ModifiableGlobalsTable(new HashRelation<>()),
				mManagedScript, mBaseSymbolTable, Collections.emptySet(), Collections.emptyMap(),
				Collections.emptyMap(), null, null, null);
		mTools = new SymbolicTools(mServices, stats, new DummyIcfg(toolkit), SimplificationTechnique.NONE,
				mBaseSymbolTable);
		final ILogger logger = mServices.getLoggingService().getLogger(getClass());
		mBaseDomain = new IntervalDomain(logger, mTools, 1, () -> ALWAYS_RUNNING_TIMER);
	}

	@After
	public void tearDown() {
		mManagedScript.unlock(this);
		mScript.exit();
	}

	@Test
	public void joinPreservesDifferentGuardBuckets() {
		final TermVariable peerLocTv = mPeerLoc.getTermVariable();
		final GuardBucketPolicy policy = new GuardBucketPolicy("worker2", peerLocTv, Map.of(1, 1, 2, 2),
				Map.of(1, Set.of(1), 2, Set.of(2)));
		final GuardSplitBucketDomain bucketDomain =
				new GuardSplitBucketDomain(mTools, mBaseDomain, Map.of("worker1", policy));
		bucketDomain.setCurrentThreadId("worker1");

		final IPredicate left = predicate(and(eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(1))));
		final IPredicate right = predicate(and(eq(varTv(mX), num(1)), eq(varTv(mPeerLoc), num(2))));

		final IPredicate baselineJoin = mBaseDomain.join(left, right);
		final IPredicate guardedJoin = bucketDomain.join(left, right);

		assertEquals(LBool.SAT, SmtUtils.checkSatTerm(mScript,
				and(baselineJoin.getFormula(), eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(2)))));
		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript,
				and(guardedJoin.getFormula(), eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(2)))));
		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript,
				and(guardedJoin.getFormula(), eq(varTv(mX), num(1)), eq(varTv(mPeerLoc), num(1)))));
	}

	@Test
	public void joinFallsBackWhenBucketCannotBeDetermined() {
		final TermVariable peerLocTv = mPeerLoc.getTermVariable();
		final GuardBucketPolicy policy = new GuardBucketPolicy("worker2", peerLocTv, Map.of(1, 1, 2, 2, 3, 3),
				Map.of(1, Set.of(1), 2, Set.of(2), 3, Set.of(3)));
		final GuardSplitBucketDomain bucketDomain =
				new GuardSplitBucketDomain(mTools, mBaseDomain, Map.of("worker1", policy));
		bucketDomain.setCurrentThreadId("worker1");

		final IPredicate left = predicate(and(eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(4))));
		final IPredicate right = predicate(and(eq(varTv(mX), num(1)), eq(varTv(mPeerLoc), num(2))));

		final IPredicate baselineJoin = mBaseDomain.join(left, right);
		final IPredicate guardedJoin = bucketDomain.join(left, right);

		assertEquals(LBool.SAT, SmtUtils.checkSatTerm(mScript,
				and(guardedJoin.getFormula(), eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(2)))));
		assertEquals(baselineJoin.getFormula().toString(), guardedJoin.getFormula().toString());
	}

	@Test
	public void joinSupportsUnaryMinusLocationLiteral() {
		final TermVariable peerLocTv = mPeerLoc.getTermVariable();
		final GuardBucketPolicy policy = new GuardBucketPolicy("worker2", peerLocTv, Map.of(-1, 1, 2, 2),
				Map.of(1, Set.of(-1), 2, Set.of(2)));
		final GuardSplitBucketDomain bucketDomain =
				new GuardSplitBucketDomain(mTools, mBaseDomain, Map.of("worker1", policy));
		bucketDomain.setCurrentThreadId("worker1");

		final IPredicate left = predicate(and(eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), neg(num(1)))));
		final IPredicate right = predicate(and(eq(varTv(mX), num(1)), eq(varTv(mPeerLoc), num(2))));

		final IPredicate guardedJoin = bucketDomain.join(left, right);

		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript,
				and(guardedJoin.getFormula(), eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(2)))));
	}

	@Test
	public void joinSupportsShiftedNotForkedLocationLiteral() {
		final TermVariable peerLocTv = mPeerLoc.getTermVariable();
		final GuardBucketPolicy policy = new GuardBucketPolicy("worker2", peerLocTv, Map.of(-1, 1, 2, 2),
				Map.of(1, Set.of(-1), 2, Set.of(2)));
		final GuardSplitBucketDomain bucketDomain =
				new GuardSplitBucketDomain(mTools, mBaseDomain, Map.of("worker1", policy));
		bucketDomain.setCurrentThreadId("worker1");

		final IPredicate left =
				predicate(and(eq(varTv(mX), num(0)), eq(num(0), mScript.term("+", varTv(mPeerLoc), num(1)))));
		final IPredicate right = predicate(and(eq(varTv(mX), num(1)), eq(varTv(mPeerLoc), num(2))));

		final IPredicate guardedJoin = bucketDomain.join(left, right);

		assertEquals(LBool.UNSAT, SmtUtils.checkSatTerm(mScript,
				and(guardedJoin.getFormula(), eq(varTv(mX), num(0)), eq(varTv(mPeerLoc), num(2)))));
	}

	private ProgramNonOldVar createIntGlobal(final String identifier) {
		final ProgramNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(identifier, mIntSort, mManagedScript, this);
		mBaseSymbolTable.add(var);
		return var;
	}

	private IPredicate predicate(final Term term) {
		return mTools.predicate(term);
	}

	private Term varTv(final ProgramNonOldVar var) {
		return var.getTermVariable();
	}

	private Term num(final int value) {
		return mScript.numeral(Integer.toString(value));
	}

	private Term neg(final Term term) {
		return mScript.term("-", term);
	}

	private Term eq(final Term lhs, final Term rhs) {
		return SmtUtils.binaryEquality(mScript, lhs, rhs);
	}

	private Term and(final Term... terms) {
		return SmtUtils.and(mScript, terms);
	}

	private static final class DummyIcfg implements IIcfg<IcfgLocation> {
		private static final long serialVersionUID = 1L;
		private final CfgSmtToolkit mToolkit;
		private IPayload mPayload;

		private DummyIcfg(final CfgSmtToolkit toolkit) {
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
		public Map<String, java.util.Set<IcfgLocation>> getProcedureErrorNodes() {
			return Collections.emptyMap();
		}

		@Override
		public java.util.Set<IcfgLocation> getLocationsOfInterest() {
			return Collections.emptySet();
		}

		@Override
		public java.util.Set<IcfgLocation> getInitialNodes() {
			return Set.of();
		}

		@Override
		public java.util.Set<IcfgLocation> getLoopLocations() {
			return Set.of();
		}

		@Override
		public String getIdentifier() {
			return "dummy";
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
}
