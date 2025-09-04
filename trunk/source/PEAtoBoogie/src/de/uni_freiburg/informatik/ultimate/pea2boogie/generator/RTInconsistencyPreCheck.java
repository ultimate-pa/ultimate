package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class RTInconsistencyPreCheck {
	public boolean mDebugReasonCOunter = true;
	public int[] reasonCounter = new int[4];

	public boolean mFullSet;

	private Script mScript;
	private ManagedScript mManagedScript;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	private IUltimateServiceProvider mServices;
	public int mCombinationNum;
	public Term mDebugTerm;
	public TermVariable mDebugVar;
	public List<ReqsWithAttributes> mListChainLinkReqs;
	public Map<TermVariable, List<ReqsWithAttributes>> mDictVar;

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mRTIReturnSet;
	public List<List<ReqsWithAttributes>> mRTICombinations;
	public Map<ReqsWithAttributes, List<ReqsWithAttributes>> mChainLinkSingles;

	public class ReqsWithAttributes {
		public String mName;
		public Phase mPenultimatePhase;
		public Phase mMaxPhase;
		public Phase mBeforeMaxPhase;
		public ReqPeas mOriginalPea;
		public PhaseEventAutomata mOriginalPeaEventAutomata;
		public Term mFullExitCondition;
		public List<Term> mExitConditions;
		public boolean mChainLinkReq;
		public CounterTrace mCounterTrace;

		public ReqsWithAttributes(final ReqPeas reqPea) {
			mOriginalPea = reqPea;
			mChainLinkReq = false;
		}

		public String getName() {
			return mName;

		}

	}

	public class Phase {
		DCPhase mDCPhase;
		Term mInvariant;
		TermVariable[] mInvariantVar;
		Term mBound;

		public Phase(final DCPhase dcPhase) {
			mDCPhase = dcPhase;

		}

	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(final List<ReqPeas> reqPeas,
			final ILogger logger, final Script script, final CddToSmt cddToSmt, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final int range, final boolean preCheckFullSet) {
		mScript = script;
		mManagedScript = managedScript;
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mServices = services;
		mRTIReturnSet = new ArrayList<>();
		mCombinationNum = range;
		mListChainLinkReqs = new ArrayList<>();
		mDictVar = new HashMap<>();
		mRTICombinations = new ArrayList<>();
		mChainLinkSingles = new HashMap<>();
		mFullSet = preCheckFullSet;

		getDebugTerm();

		// --------START OF RTI CHECK----------------
		getAttributes(reqPeas);
		findSinglesForChains();
		// If the preference "full Set" is set, the maximum chain link depth is set to the number of chainLink
		// requirements
		mCombinationNum = mFullSet ? mListChainLinkReqs.size() : mCombinationNum;
		rtiCheckSingles();
		rtiCheckChainLinkReqs();
		mLogger.info("Number of chain link requirements: " + mListChainLinkReqs.size()); // Print out found sets
		for (final ReqsWithAttributes r : mListChainLinkReqs) { // prints names of chain-link requirements (for debug
																// reasons)
			mLogger.info("   " + r.mName);
		}
		printResults();
		return mRTIReturnSet; // returns found sets in format for checking to reduce false positives

	}

	private void printResults() {
		mLogger.info("-------------------RTI PreCheck found " + mRTIReturnSet.size() + " sets----------------------");
		for (final Entry<PatternType<?>, PhaseEventAutomata>[] entry : mRTIReturnSet) {
			final StringBuilder sb = new StringBuilder();
			sb.append("[");
			for (final Entry<PatternType<?>, PhaseEventAutomata> e : entry) {
				sb.append(e.getValue().getName() + " ");
			}
			sb.append("]");
			mLogger.info(sb.toString());
		}
	}

	/**
	 * checks for each chain-link requirement potential singles. This reduces checking later.
	 *
	 * @param gets
	 *            the list mListChainLinkReqs and mChainLinkSingles
	 */
	private void findSinglesForChains() {

		for (final ReqsWithAttributes req : mListChainLinkReqs) {
			final List<ReqsWithAttributes> singles = mChainLinkSingles.computeIfAbsent(req, r -> new ArrayList<>());

			// avoid duplicates if the same otherReq appears via multiple variables
			final var seen = new java.util.LinkedHashSet<ReqsWithAttributes>();

			for (final TermVariable var : req.mFullExitCondition.getFreeVars()) {
				for (final ReqsWithAttributes other : mDictVar.getOrDefault(var, java.util.List.of())) {
					if (other != req && ChainLinkTest(req, other) && seen.add(other)) {
						singles.add(other);
					}
				}
			}
		}

	}

	/**
	 * Checks if a chain-link and a single can possible match. So if they deal with the same variable and if it is
	 * possible that the conjunction of the max phases are possible
	 *
	 * @param req1
	 * @param req2
	 * @return
	 */
	private boolean ChainLinkTest(final ReqsWithAttributes req1, final ReqsWithAttributes req2) {
		if (!haveIntersection(req1.mFullExitCondition.getFreeVars(), req2.mFullExitCondition.getFreeVars())) {
			return false; // intersection not found
		}
		if (((req1.mBeforeMaxPhase != null && req2.mBeforeMaxPhase != null)
				&& req1.mPenultimatePhase.mBound.equals(req2.mPenultimatePhase.mBound))
				&& (req1.mPenultimatePhase.mBound == req2.mPenultimatePhase.mBound)) {

			final Term conjunction =
					SmtUtils.and(mScript, req1.mBeforeMaxPhase.mInvariant, req2.mBeforeMaxPhase.mInvariant);
			final LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
			if (result == LBool.UNSAT) {

				return false;

			}
		}

		return true;

	}

	public static boolean haveIntersection(final TermVariable[] vars1, final TermVariable[] variables) {
		for (final TermVariable elem : variables) {
			if (Arrays.asList(vars1).contains(elem)) {
				return true; // intersection of variables found
			}
		}
		return false; // do not contain same variable-> no further checking needed
	}

	/**
	 * Iterates over all chain-link requirements and tries to build combinations up to the configured maximum size
	 * (mCombinationNum). For each depth, it starts recursive exploration with each element as the initial chain link.
	 */
	private void rtiCheckChainLinkReqs() {
		if (mCombinationNum <= 0) {
			return;
		}

		for (int depth = 1; depth <= mCombinationNum; depth++) {
			mLogger.info("-------------- DEPTH (number of chain links)" + depth + "------------------");
			double progressCounter = 0.0f;
			int maxSets = mListChainLinkReqs.size() * (mListChainLinkReqs.size() - 1) / depth;
			mLogger.info("Max number of chains to check:" + maxSets);
			for (int i = 0; i < mListChainLinkReqs.size(); i++) {
				// Simple progress indicator
				final float progress = (i * 100.0f) / mListChainLinkReqs.size();
				if (progress > (progressCounter + 1.0f)) {
					progressCounter = progress;
					mLogger.info(
							"STATUS: depth: " + depth + " out of " + mCombinationNum + ": " + (int) progress + "%");
					maxSets = (mListChainLinkReqs.size() - i) * (mListChainLinkReqs.size() - 1 - i) / depth;
					mLogger.info("max number of chains remaining: " + maxSets);

				}

				// Start a new chain link result set with one element
				final List<ReqsWithAttributes> chainLinkRes = new ArrayList<>();
				chainLinkRes.add(mListChainLinkReqs.get(i));

				// Pass exit conditions of the first element + all following as remaining candidates
				addChainLinkRecursive(chainLinkRes, depth, mListChainLinkReqs.get(i).mExitConditions,
						new ArrayList<>(mListChainLinkReqs.subList(i + 1, mListChainLinkReqs.size())));
			}
		}
	}

	/**
	 * Creates a set of chain-link-requirements with the size of "depth". Therefore checks if the chain links can form a
	 * "chain".
	 *
	 * @param chainLinkRes
	 * @param depth
	 * @param exitConditions
	 * @param remainingChainLinks
	 */
	private void addChainLinkRecursive(final List<ReqsWithAttributes> chainLinkRes, final int depth,
			final List<Term> exitConditions, final List<ReqsWithAttributes> remainingChainLinks) {

		// Target size reached → look for singles that fit this chain
		if (chainLinkRes.size() == depth) {
			findSinglesForChains(chainLinkRes, exitConditions);
			return;
		}

		// More chain links required, but no candidates left
		if (remainingChainLinks.isEmpty()) {
			mLogger.debug("No remaining chain links");
			return;
		}

		mLogger.debug("Add chain link, remaining: {}", remainingChainLinks.size());

		for (int i = 0; i < remainingChainLinks.size(); i++) {
			final ReqsWithAttributes candidate = remainingChainLinks.get(i);

			for (final Term exitA : exitConditions) {
				for (final Term exitB : candidate.mExitConditions) {
					final Term conj = SmtUtils.and(mScript, exitA, exitB);
					final LBool sat = SmtUtils.checkSatTerm(mScript, conj);

					// We need disjoint exit conditions here (i.e., NOT SAT)
					if (sat == LBool.SAT) {
						continue;
					}
					// Add next chain link
					final List<ReqsWithAttributes> nextChain = new ArrayList<>(chainLinkRes);
					nextChain.add(candidate);

					// Remove the two exit conditions we just paired (identity-based removal preserved intentionally)
					final List<Term> nextExit =
							new ArrayList<>(exitConditions.size() + candidate.mExitConditions.size() - 2);

					for (final Term ec : exitConditions) {
						if (ec != exitA) {
							nextExit.add(ec);
						}
					}
					for (final Term ec : candidate.mExitConditions) {
						if (ec != exitB) {
							nextExit.add(ec);
						}
					}

					// Remaining candidates to the right of i
					final int nextIndex = i + 1;
					if (nextIndex < remainingChainLinks.size()) {
						final List<ReqsWithAttributes> tail =
								new ArrayList<>(remainingChainLinks.subList(nextIndex, remainingChainLinks.size()));
						addChainLinkRecursive(nextChain, depth, nextExit, tail);
					}
				}
			}
		}
	}

	/**
	 * For a set of chain link requirements finds all potential singles. -> Singles that fit to the chain-link
	 * requirements This is done to reduce the possible singles for a chain test
	 *
	 * @param chainLinkRes
	 * @param exitConditions
	 */
	private void findSinglesForChains(final List<ReqsWithAttributes> chainLinkRes, final List<Term> exitConditions) {

		mLogger.debug("Finding singles for chain link requirements: ");
		mLogger.debug("new Chain set:");
		for (final ReqsWithAttributes r : chainLinkRes) {
			mLogger.debug("   " + r.mName);
		}

		List<ReqsWithAttributes> potentialSingles = new ArrayList<>();
		if (chainLinkRes.size() == 1) {
			potentialSingles = mChainLinkSingles.get(chainLinkRes.get(0));
		} else {
			for (final ReqsWithAttributes req : chainLinkRes) {
				potentialSingles.addAll(mChainLinkSingles.get(req));

			}
		}
		if (potentialSingles.isEmpty()) {
			mLogger.debug("No potential singles found");
			return;
		}
		mLogger.debug("Potential singles found: " + potentialSingles.size());
		fillWithSinglesRecursive(potentialSingles, chainLinkRes, exitConditions, new ArrayList<>());

	}

	/**
	 * For a list of chainLinkReqs which are possible rt-inconsistent: try to fill with singles to create a
	 * rt-inconsitency. This is done recursive, adding one single after another. Tries to eliminate the exit options
	 * from the combined chain link. If no exit options are left-> Possible rt-inconsistency
	 *
	 * @param potentialSingles
	 * @param chainLinkRes
	 * @param exitConditions
	 * @param usedSingles
	 */
	private void fillWithSinglesRecursive(final List<ReqsWithAttributes> potentialSingles,
			final List<ReqsWithAttributes> chainLinkRes, final List<Term> exitConditions,
			final List<ReqsWithAttributes> usedSingles) {
		mLogger.debug("add single, potential singles left: " + potentialSingles.size());

		// optional short-circuits
		if (potentialSingles.isEmpty()) {
			return;
		}
		if (exitConditions.isEmpty()) {
			// already disjoint → found an RTI candidate
			chainLinkRtiFoundCheck(chainLinkRes, usedSingles);
			return;
		}

		for (int i = 0; i < potentialSingles.size(); i++) {
			final ReqsWithAttributes candidate = potentialSingles.get(i);

			// filter exit conditions that remain feasible with this candidate
			final List<Term> reducedExitConditions = new ArrayList<>();
			for (final Term ec : exitConditions) {
				final Term conj = SmtUtils.and(mScript, ec, candidate.mFullExitCondition);
				if (SmtUtils.checkSatTerm(mScript, conj) == LBool.SAT) {
					reducedExitConditions.add(ec); // keep ec (filter), or add 'conj' if you intend to strengthen
				}
			}

			if (reducedExitConditions.size() == exitConditions.size()) {
				mLogger.debug("No reduction of exit conditions for {}", candidate.mName);
				continue; // nothing gained by choosing this candidate now
			}

			// take candidate into the current path
			final List<ReqsWithAttributes> newUsedSingles = new ArrayList<>(usedSingles);
			newUsedSingles.add(candidate);

			if (reducedExitConditions.isEmpty()) {
				// All ECs eliminated → check and record RTI
				chainLinkRtiFoundCheck(chainLinkRes, newUsedSingles);
			} else {

				final List<ReqsWithAttributes> tail =
						new ArrayList<>(potentialSingles.subList(i + 1, potentialSingles.size()));

				fillWithSinglesRecursive(tail, chainLinkRes, reducedExitConditions, newUsedSingles);
			}
		}
	}

	/**
	 * Checks for sets > 2 if the set is rt-inconsistent If rt-inconsistent -> adds them to mRTIReturnSet
	 */
	private void chainLinkRtiFoundCheck(final List<ReqsWithAttributes> chainLinkRes,
			final List<ReqsWithAttributes> usedSingles) {
		for (final List<ReqsWithAttributes> rtiSet : mRTICombinations) {

			if (usedSingles.containsAll(rtiSet)) {

				mLogger.debug("set not minimal");
				return;
			}

		}

		final List<ReqsWithAttributes> fullSet = new ArrayList<>(chainLinkRes);
		fullSet.addAll(usedSingles);
		// check for exit conditions
		Term conjunction = fullSet.get(0).mFullExitCondition;

		for (int i = 1; i < fullSet.size(); i++) {
			conjunction = SmtUtils.and(mScript, conjunction, fullSet.get(i).mFullExitCondition);
		}

		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {
			mLogger.debug("set not disjoint");
			return;
		}
		// check if max phases are all valid together
		conjunction = fullSet.get(0).mMaxPhase.mInvariant;

		for (int i = 1; i < fullSet.size(); i++) {
			conjunction = SmtUtils.and(mScript, conjunction, fullSet.get(i).mMaxPhase.mInvariant);
		}

		result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result == LBool.UNSAT) {
			mLogger.debug("set not disjoint");
			return;
		}
		// if we reach this point the set is rt-inconsistent
		mLogger.debug("Rt-inconsistent set with chain-link found:");
		for (final ReqsWithAttributes r : fullSet) {
			mLogger.debug("   " + r.mName);
		}
		mRTIReturnSet.add(rtiSetsFormatted(fullSet));
	}

	/**
	 * Creates a debug term variable which is needed for DCPhase to SMT
	 */
	public void getDebugTerm() {
		// BIG TODO, workaround
		final Logics logic = Logics.QF_UFNIA;
		final Theory theo = new Theory(logic);
		final Term rhs = mScript.decimal(Double.toString(2.0));
		final Sort sort2 = rhs.getSort();
		mDebugVar = theo.createTermVariable("debugVar", sort2);
	}

	/**
	 * Checks for all non-chain-link requirement, so for set size 2, for rt-inconsistencies.
	 *
	 */
	private void rtiCheckSingles() {

		for (final Map.Entry<TermVariable, List<ReqsWithAttributes>> e : mDictVar.entrySet()) {
			final List<ReqsWithAttributes> reqs = e.getValue();
			if (reqs == null || reqs.size() < 2) {
				continue;
			}

			final List<List<ReqsWithAttributes>> combinations = combinations2(reqs);

			for (final List<ReqsWithAttributes> pair : combinations) {
				final ReqsWithAttributes a = pair.get(0);
				final ReqsWithAttributes b = pair.get(1);

				// canonical key (unordered pair)
				final String k1 = a.getName();
				final String k2 = b.getName();

				final List<ReqsWithAttributes> canonicalPair =
						(k1.compareTo(k2) <= 0) ? java.util.List.of(a, b) : java.util.List.of(b, a);

				if (mRTICombinations.contains(canonicalPair)) {
					continue; // already checked/recorded this combination
				}
				mRTICombinations.add(canonicalPair);

				if (rtiCheckFor2Reqs(a, b)) {
					mLogger.debug("RTI found for:" + a.mName + " and " + b.mName);
					mRTIReturnSet.add(rtiSetsFormatted(canonicalPair));

				}
			}
		}
	}

	/**
	 * Checks for 2 non-chain-link requirements if they are rt-inconsistent
	 *
	 * @param req1
	 * @param req2
	 * @return rt-inconsistent -> true not rt-inconsistent -> false
	 */
	private boolean rtiCheckFor2Reqs(final ReqsWithAttributes r1, final ReqsWithAttributes r2) {
		// 1)exit condition check
		Term conj = SmtUtils.and(mScript, r1.mFullExitCondition, r2.mFullExitCondition);
		LBool res = SmtUtils.checkSatTerm(mScript, conj);
		if (res != LBool.UNSAT) {
			return failReason(0, "Exit conditions overlap or UNKNOWN");
		}

		// 2) before max phase check
		if (r1.mBeforeMaxPhase != null && r2.mBeforeMaxPhase != null
				&& safeEquals(r1.mPenultimatePhase.mBound, r2.mPenultimatePhase.mBound)) {

			conj = SmtUtils.and(mScript, r1.mBeforeMaxPhase.mInvariant, r2.mBeforeMaxPhase.mInvariant);
			res = SmtUtils.checkSatTerm(mScript, conj);
			if (res == LBool.UNSAT) {
				return failReason(3, "beforeMax invariants incompatible (UNSAT)");
			}
		}

		// 3) Max-Phases have to be compatible
		if (r1.mMaxPhase == null || r2.mMaxPhase == null) {
			return failReason(4, "missing max phase");
		}
		conj = SmtUtils.and(mScript, r1.mMaxPhase.mInvariant, r2.mMaxPhase.mInvariant);
		res = SmtUtils.checkSatTerm(mScript, conj);
		if (res == LBool.UNSAT) {
			return failReason(1, "max invariants incompatible (UNSAT)");
		}

		// if 1-3 do not fail return true -> requirements are rt-inconsistent
		return true;
	}

	private boolean failReason(final int idx, final String msg) {
		if (mDebugReasonCOunter) {
			reasonCounter[idx]++;
			mLogger.debug("rtiCheckFor2Reqs: {}", msg);

		}
		return false;
	}

	private static boolean safeEquals(final Object a, final Object b) {
		return (a == b) || (a != null && a.equals(b));
	}

	/**
	 * finds all combinations of a set with the size of two
	 *
	 * @param args
	 * @return
	 */
	public static List<List<ReqsWithAttributes>> combinations2(final List<ReqsWithAttributes> args) {
		final List<List<ReqsWithAttributes>> pairs = new ArrayList<>();
		for (int i = 0; i < args.size(); i++) {
			for (int j = i + 1; j < args.size(); j++) {
				pairs.add(Arrays.asList(args.get(i), args.get(j)));
			}
		}
		return pairs;
	}

	/**
	 * Populate attributes for each requirement/countertrace pair. - Extracts penultimate/max/before-max phases (with
	 * bounds & invariants). - Computes full exit condition (DNF of the negated penultimate invariant). - Classifies
	 * requirements into chain-link vs. non-chain-link by EC count. - Indexes non-chain-link requirements by free
	 * variables of the penultimate invariant.
	 */
	private void getAttributes(final List<ReqPeas> reqPeas) {
		for (final ReqPeas reqPea : reqPeas) {
			for (final Map.Entry<CounterTrace, PhaseEventAutomata> child : reqPea.getCounterTrace2Pea()) {

				final CounterTrace ct = child.getKey();
				final PhaseEventAutomata pea = child.getValue();
				final DCPhase[] phases = ct.getPhases();
				final int n = phases.length;

				// We need at least 2 phases to have a "penultimate"
				if (n < 2) {
					mLogger.warn("CounterTrace too short ({} phases) for {}", n, pea.getName());
					continue;
				}

				final ReqsWithAttributes req = new ReqsWithAttributes(reqPea);
				req.mName = pea.getName();
				req.mOriginalPeaEventAutomata = pea;
				req.mCounterTrace = ct;

				// --------------------------
				// Penultimate phase (always exists because n >= 2)
				// --------------------------
				final DCPhase penultDC = phases[n - 2];
				req.mPenultimatePhase = new Phase(penultDC);
				req.mPenultimatePhase.mInvariant = mCddToSmt.toSmt(penultDC.getInvariant());
				req.mPenultimatePhase.mInvariantVar = req.mPenultimatePhase.mInvariant.getFreeVars();
				req.mPenultimatePhase.mBound = boundToSmt(req.mPenultimatePhase);

				// Full exit condition = DNF(not(penult invariant))
				final Term negInv = SmtUtils.not(mScript, req.mPenultimatePhase.mInvariant);
				req.mFullExitCondition = SmtUtils.toDnf(mServices, mManagedScript, negInv);
				req.mExitConditions = new ArrayList<>(Arrays.asList(SmtUtils.getDisjuncts(req.mFullExitCondition)));

				// --------------------------
				// Max / Before-Max phase selection
				// --------------------------
				// If penultimate has a bound, then penultimate is the "max" phase,
				// otherwise the max is one step earlier (n-3).
				final boolean penultHasBound = penultDC.getBoundType() != 0;
				final int maxIdxFromEnd = penultHasBound ? 2 : 3; // n-2 or n-3
				final int beforeIdxFromEnd = penultHasBound ? 3 : 4; // n-3 or n-4

				// Guard against short traces
				if (n - maxIdxFromEnd < 0) {
					mLogger.warn("Cannot determine max phase (n={}) for {}", n, pea.getName());
					continue;
				}

				req.mMaxPhase = new Phase(phases[n - maxIdxFromEnd]);
				req.mMaxPhase.mInvariant = mCddToSmt.toSmt(req.mMaxPhase.mDCPhase.getInvariant());
				req.mMaxPhase.mInvariantVar = req.mMaxPhase.mInvariant.getFreeVars();
				req.mMaxPhase.mBound = boundToSmt(req.mMaxPhase);

				if (n - beforeIdxFromEnd >= 0) {
					req.mBeforeMaxPhase = new Phase(phases[n - beforeIdxFromEnd]);
					req.mBeforeMaxPhase.mInvariant = mCddToSmt.toSmt(req.mBeforeMaxPhase.mDCPhase.getInvariant());
					req.mBeforeMaxPhase.mInvariantVar = req.mBeforeMaxPhase.mInvariant.getFreeVars();
					req.mBeforeMaxPhase.mBound = boundToSmt(req.mBeforeMaxPhase);
				} else {
					req.mBeforeMaxPhase = null;
				}

				// --------------------------
				// Chain-link classification and variable index
				// --------------------------
				if (req.mExitConditions.size() > 1) {
					// multiple disjuncts → chain-link candidate
					req.mChainLinkReq = true;
					mListChainLinkReqs.add(req);
				} else {
					// single EC → index by free vars of the *penultimate invariant*
					final TermVariable[] vars = req.mPenultimatePhase.mInvariantVar;
					if (vars != null) {
						for (final TermVariable v : vars) {
							mDictVar.computeIfAbsent(v, k -> new ArrayList<>()).add(req);
						}
					}
				}
			}
		}
	}

	/**
	 * Formats the found rt-inconsistencies into format of the rt-inconsistency check
	 */

	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(final List<ReqsWithAttributes> reqs) {
		return reqs.stream()
				.map(req -> new AbstractMap.SimpleEntry<>(req.mOriginalPea.getPattern(), req.mOriginalPeaEventAutomata))
				.sorted(Comparator.comparing(Entry::getValue)).toArray(Entry[]::new);
	}

	/**
	 * Creates for the given phase a new term from the bound of the DCPhase. for all terms an extra debug variable is
	 * used. Allows to compare time bounds from phases later
	 *
	 * @param phase
	 * @return Term
	 */
	private Term boundToSmt(final Phase phase) {
		final int bt = phase.mDCPhase.getBoundType();
		if (bt == 0) {
			return mScript.term("true");
		}

		final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
		switch (bt) {
		case 2:
			return SmtUtils.greater(mScript, mDebugVar, rhs); // >
		case 1:
			return SmtUtils.geq(mScript, mDebugVar, rhs); // >=
		case -2:
			return SmtUtils.less(mScript, mDebugVar, rhs); // <
		default:
			return SmtUtils.leq(mScript, mDebugVar, rhs); // <= (covers -1 and others)
		}
	}
}
