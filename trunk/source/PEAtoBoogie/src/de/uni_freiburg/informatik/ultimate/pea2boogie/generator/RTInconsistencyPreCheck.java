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
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
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

/**
 * RTInconsistencyPreCheck ----------------------- Purpose This class computes *candidates* for real-time
 * inconsistencies (RTIs) among a set of requirements expressed as Phase Event Automata (PEA). The class does a
 * lightweight, aggressively-pruned search that rules out obviously impossible combinations early and produces small
 * sets of requirements that are *likely* inconsistent. A subsequent, sound (and more expensive) check can then verify
 * them.
 *
 * Key Concepts - CounterTrace / DCPhase: A PEA trace decomposed into phases, each with an invariant (state guard) and
 * possibly a time bound. We reason about “penultimate”, “max”, and “before-max” phases. - Exit condition (EC): The
 * negation of the penultimate invariant, in Disjunctive Normal Form (DNF). For chain-link requirements, the EC is a
 * disjunction with multiple literals, e.g. (A ∨ B). For singles, it is a single literal. - Chain-link requirements:
 * Requirements with multiple exit options (EC has >1 disjunct). They can “dock” with others by having mutually UNSAT
 * exit pairs (e.g. B with ¬B), enabling chain construction. - Singles: Requirements with a single exit clause; they can
 * eliminate remaining exit options of a chain. - Friends: Two chain-links are “friends” if they have at least one pair
 * of mutually UNSAT exit options *and* their “max” phases are mutually SAT. Friends can appear together in a chain.
 *
 * Overall Algorithm (very high level) 1) Extract attributes per requirement (invariants, time-bounds, ECs in DNF,
 * max/before-max phases). 2) Partition into chain-links vs singles. Index singles by variables to quickly find
 * candidates sharing vars. 3) For each chain-link, precompute: - Fitting singles (EC UNSAT with one chain EC; max
 * phases SAT). - “Friend” chain-links (EC UNSAT across some pair; max phases SAT). 4) Explore chain depths
 * (1..configured/max), building chains only from friend relationships to avoid explosion. 5) For each chain, remove the
 * matched EC pairs used to dock links; try adding singles that eliminate the remaining ECs. Any combination that
 * eliminates all ECs *and* has compatible max phases becomes an RTI candidate. 6) For pairs of singles (no chain
 * links), apply a simpler two-req precheck (EC disjoint + max phases compatible). 7) Return candidates in the format
 * expected by the subsequent sound checker.
 *
 * Notes - The class uses SMT queries via SmtUtils/Script(LBool) to check SAT/UNSAT of term conjunctions. - Many data
 * structures are “helper indices” that reduce combinatorial blow-up. - This is a precheck: results minimize false
 * negatives (by pruning impossible cases) and reduce false positives as much as possible, but final verification is
 * left to a sound RTI check after this phase.
 */
public class RTInconsistencyPreCheck {

	// ---------------- Debug helpers (not required for the algorithm’s correctness)

	/** If true, collect rough reason counts (kept but not currently used). */
	public boolean mDebugReasonCOunter = true;

	/** Buckets for optional reason counting. */
	public int[] reasonCounter = new int[4];

	// ---------------- Services / environment

	/** Raw SMT script used to build/solve formulae. */
	private Script mScript;

	/** Managed script for utility operations like DNF conversion. */
	private ManagedScript mManagedScript;

	/** Logger supplied by the tool framework. */
	private ILogger mLogger;

	/** Translator from CDD (PEA conditions) to SMT terms. */
	private CddToSmt mCddToSmt;

	/** Ultimate service provider handle (needed by SmtUtils helpers). */
	private IUltimateServiceProvider mServices;

	// ---------------- Configuration

	/** If true, explore chains up to the number of all chain-link requirements. */
	public boolean mFullSet;

	/** Max number of chain-links per chain (depth); overridden by mFullSet. */
	public int mCombinationNum;

	/**
	 * If true, this component stops after the pre-check and does not forward candidates to the sound checker. Useful
	 * during experimentation or for statistics/debugging.
	 */
	public boolean mRTIPreCheckOnly = false;

	// ---------------- Internal helper terms for bound comparison

	/**
	 * A dummy term/variable used to encode phase time bounds into SMT. Phases compare their bounds by constructing
	 * simple constraints over this variable (e.g., debugVar ≤ 5).
	 */
	public Term mDebugTerm;
	public TermVariable mDebugVar;

	// ---------------- Working sets for the algorithm

	public List<ReqsWithAttributes> mListAllReqs;

	/** All chain-link requirements (EC has more than one disjunct) with derived attributes. */
	public List<ReqsWithAttributes> mListChainLinkReqs;

	/**
	 * Index of *single* requirements by free variables in their penultimate invariant. Key: a TermVariable present in a
	 * single’s penultimate invariant. Value: list of single ReqsWithAttributes that reference that variable. Note:
	 * Chain-links are *not* indexed here.
	 */
	public Map<TermVariable, List<ReqsWithAttributes>> mDictVar;

	/**
	 * Final result for the *sound* RTI checker, i.e., RTI candidate sets translated back into (PatternType, PEA). Each
	 * array entry is one candidate set.
	 */
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mRTIReturnSet;

	/** Internal representation of RTI candidate sets as requirement attribute objects. */
	public List<List<ReqsWithAttributes>> mRTICombinations;

	/**
	 * For each chain-link requirement, the prefiltered singles that could help closing the chain: (a) at least one
	 * single’s EC is UNSAT with one chain EC, and (b) critical (max) phases are mutually SAT.
	 */
	public Map<ReqsWithAttributes, List<ReqsWithAttributes>> mChainLinkSingles;

	/**
	 * For each chain-link requirement, the other chain-links it can connect to (“friends”): there exists an UNSAT EC
	 * pair and their max phases are SAT.
	 */
	public Map<ReqsWithAttributes, List<ReqsWithAttributes>> mChainLinkFriends;

	// ---------------- Scratch data for recursive construction of chains/singles

	public List<List<ReqsWithAttributes>> combinationsHelper; // stores friend-based chains before validation
	public List<List<Term>> LeftOverExitConditionsHelper; // remaining EC lists after docking steps
	public int helperCounter; // simple counter for combinational attempts

	// debug var to print out stuff
	public boolean printAllExitConditions = false;
	// ================================================================================================================
	// Data containers used during the precheck
	// ================================================================================================================

	/**
	 * ReqsWithAttributes A thin “view” over a requirement/PEA, storing both original objects and the precomputed SMT
	 * attributes we need for pruning and construction (ECs, important phases, timing flags).
	 */
	public class ReqsWithAttributes {
		public boolean mTimed; // true if the requirement involves clocks/time bounds
		public String mName; // PEA name (e.g., "ID0002_ct1"), used as stable identifier
		public Phase mPenultimatePhase; // phase used to define the exit condition (negated invariant)
		public Phase mMaxPhase; // phase whose invariant must be SAT with others in a candidate
		public Phase mBeforeMaxPhase; // optional: for additional pruning (currently rarely used)
		public ReqPeas mOriginalPea; // original SRParse pattern wrapper (“ReqPeas”)
		public PhaseEventAutomata mOriginalPeaEventAutomata; // the concrete PEA we reason about
		public Term mFullExitCondition; // DNF(not(penultimateInvariant))
		public List<Term> mExitConditions; // the individual disjuncts (literals) of the EC DNF
		public boolean mChainLinkReq; // true if EC has >1 disjunct
		public CounterTrace mCounterTrace; // original trace for context/debug

		public ReqsWithAttributes(final ReqPeas reqPea) {
			mOriginalPea = reqPea;
			mChainLinkReq = false;
		}

		/** Copy constructor used for “seeping” variants. */
		public ReqsWithAttributes(final ReqsWithAttributes other) {
			mTimed = other.mTimed;
			mName = other.mName;
			mPenultimatePhase = other.mPenultimatePhase;
			mMaxPhase = other.mMaxPhase;
			mBeforeMaxPhase = other.mBeforeMaxPhase;
			mOriginalPea = other.mOriginalPea;
			mOriginalPeaEventAutomata = other.mOriginalPeaEventAutomata;
			mFullExitCondition = other.mFullExitCondition;
			mExitConditions = other.mExitConditions;
			mChainLinkReq = other.mChainLinkReq;
			mCounterTrace = other.mCounterTrace;
		}

		public String getName() {
			return mName;
		}
	}

	/** Simple wrapper for a DCPhase with its invariant, free variables and a normalized time-bound constraint. */
	public class Phase {
		DCPhase mDCPhase;
		Term mInvariant; // SMT encoding of the phase invariant
		TermVariable[] mInvariantVar; // free variables mentioned in the invariant (used for indexing)
		Term mBound; // SMT encoding of the bound using mDebugVar (e.g., debugVar ≤ 5)

		public Phase(final DCPhase dcPhase) {
			mDCPhase = dcPhase;
		}
	}

	// ================================================================================================================
	// Entry point
	// ================================================================================================================

	/**
	 * Run the RTI precheck on a set of requirements.
	 *
	 * @param reqPeas
	 *            The requirements (pattern + PEA trace pairs).
	 * @param logger
	 *            Logger for progress and diagnostics.
	 * @param script
	 *            SMT solver connection.
	 * @param cddToSmt
	 *            Translator for PEA conditions to SMT.
	 * @param services
	 *            Service provider required by SmtUtils helpers.
	 * @param managedScript
	 *            SMT manager used for higher-level operations (e.g., DNF).
	 * @param range
	 *            Max chain depth (number of chain-links). Overridden by mFullSet if enabled.
	 * @param preCheckFullSet
	 *            If true, set depth = number of chain-links (try the “full” search).
	 * @param onlyPreCheck
	 *            If true, return no candidates to the next stage (useful when this step is used stand-alone).
	 * @return Candidate sets formatted for the sound RTI check.
	 */
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(final List<ReqPeas> reqPeas,
			final ILogger logger, final Script script, final CddToSmt cddToSmt, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final int range, final boolean preCheckFullSet,
			final boolean onlyPreCheck) {

		// --- wiring / configuration
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
		mChainLinkFriends = new HashMap<>();
		mListAllReqs = new ArrayList<>();
		mFullSet = preCheckFullSet;
		mRTIPreCheckOnly = onlyPreCheck;

		// set up the synthetic “debugVar” so we can express time bounds as simple comparisons
		getDebugTerm();

		// 1) Extract all attributes we need for pruning and composition
		getAttributes(reqPeas);

		// status output: how many chain-link requirements did we find?
		mLogger.info("Number of chain link requirements: " + mListChainLinkReqs.size());
		for (final ReqsWithAttributes r : mListChainLinkReqs) {
			mLogger.info("   " + r.mName);
		}

		// 2) Precompute compatibilities to aggressively prune later searches
		findSinglesForChains(); // for each chain-link, which singles might help close it?
		findFriendsForChains(); // for each chain-link, which other chain-links can it dock with?

		// If “full set” requested, search up to the entire number of chain-links
		mCombinationNum = mFullSet ? mListChainLinkReqs.size() : mCombinationNum;
		mLogger.info("Sort done, starting RTI PreCheck...");

		if (printAllExitConditions) {
			mLogger.info("Exit-Conditions");

			for (final ReqsWithAttributes req : mListAllReqs) {
				mLogger.info(req.mName + ": " + req.mFullExitCondition);
			}
		}

		// 3) Precheck pairs of singles (no chain-links involved)
		rtiCheckSingles();

		// 4) Precheck combinations involving one or more chain-links
		rtiCheckChainLinkReqs();

		// 5) Convert internal representation into the format expected by the downstream checker
		for (final List<ReqsWithAttributes> rtis : mRTICombinations) {
			mRTIReturnSet.add(rtiSetsFormatted(rtis));
		}

		printResults();

		if (mRTIPreCheckOnly) {
			mLogger.warn("RTI PreCheck only, stopping here. Note: results are not verified by the sound checker.");
			return new ArrayList<>();
		}
		return mRTIReturnSet;
	}

	// ================================================================================================================
	// Friend / compatibility computation (chain-link ↔ chain-link)
	// ================================================================================================================

	/**
	 * For every chain-link requirement, find other chain-links it can “dock” with (“friends”). Two chain-links A and B
	 * are friends if: - There exists at least one pair of exit options a∈EC(A), b∈EC(B) s.t. a ∧ b is UNSAT (i.e.,
	 * disjoint), and - Their critical “max” phases are jointly SAT (i.e., feasible together). We build a symmetric
	 * adjacency list mChainLinkFriends to restrict chain search to viable neighbors only.
	 */
	private void findFriendsForChains() {
		mLogger.info("Finding friends for chain-link requirements, this might take a while...");

		// Initialize adjacency lists
		for (final ReqsWithAttributes req : mListChainLinkReqs) {
			mChainLinkFriends.put(req, new ArrayList<>());
		}

		// Quadratic scan over chain-links; asymmetric pairs i<j to avoid duplicate checks
		for (int i = 0; i < mListChainLinkReqs.size(); i++) {
			final ReqsWithAttributes a = mListChainLinkReqs.get(i);

			for (int j = i + 1; j < mListChainLinkReqs.size(); j++) {
				final ReqsWithAttributes b = mListChainLinkReqs.get(j);

				// (1) Must have at least one UNSAT EC pair
				if (!checkExitOptionsDisjoint(a, b)) {
					continue;
				}

				// (2) Max phases must be compatible (SAT)
				if (!checkMaxPhaseDisjoint(a, b)) {
					continue;
				}

				// (3) Don’t pair a requirement with itself (by name equality)
				if (a.mOriginalPeaEventAutomata.getName() == b.mOriginalPeaEventAutomata.getName()) {
					continue;
				}

				// We have a friend relation; store both directions
				mChainLinkFriends.get(a).add(b);
				mChainLinkFriends.get(b).add(a);
			}
		}
	}

	/** Return true if both max-phase invariants are mutually SAT; false if UNSAT or data missing. */
	private boolean checkMaxPhaseDisjoint(final ReqsWithAttributes req, final ReqsWithAttributes other) {
		if (req.mMaxPhase == null || other.mMaxPhase == null) {
			// Defensive: if a max phase is missing, we conservatively keep the pair (don’t prune).
			mLogger.warn("checkMaxPhaseDisjoint: missing max phase");
			return true;
		}
		final Term conj = SmtUtils.and(mScript, req.mMaxPhase.mInvariant, other.mMaxPhase.mInvariant);
		final LBool sat = SmtUtils.checkSatTerm(mScript, conj);
		return sat != LBool.UNSAT;
	}

	/**
	 * Return true iff there exists at least one pair (a,b) with a∈EC(req), b∈EC(other) such that a∧b is UNSAT. This is
	 * the “docking” criterion that allows two chain-links to connect.
	 */
	private boolean checkExitOptionsDisjoint(final ReqsWithAttributes req, final ReqsWithAttributes other) {
		for (final Term exitA : req.mExitConditions) {
			for (final Term exitB : other.mExitConditions) {
				final Term conj = SmtUtils.and(mScript, exitA, exitB);
				final LBool sat = SmtUtils.checkSatTerm(mScript, conj);
				if (sat != LBool.SAT) { // i.e., UNSAT or UNKNOWN → treat as potentially disjoint (conservative)
					return true;
				}
			}
		}
		return false;
	}

	/** Pretty print the final candidate sets for logging. */
	private void printResults() {
		mLogger.info("-------------------RTI PreCheck found " + mRTIReturnSet.size() + " sets----------------------");
		for (final Entry<PatternType<?>, PhaseEventAutomata>[] entry : mRTIReturnSet) {
			final StringBuilder sb = new StringBuilder();
			sb.append("[");
			for (final Entry<PatternType<?>, PhaseEventAutomata> e : entry) {
				sb.append(e.getValue().getName()).append(" ");
			}
			sb.append("]");
			mLogger.info(sb.toString());
		}
	}

	// ================================================================================================================
	// Chain-link → single prefiltering
	// ================================================================================================================

	/**
	 * For every chain-link, precompute the set of “fitting” singles that might help eliminating remaining ECs. A single
	 * “fits” a chain-link if: - The single’s *full* EC is UNSAT with at least one chain EC, and - The max phases are
	 * mutually SAT (when applicable). Results are stored in mChainLinkSingles to prune later searches when attaching
	 * singles to chains.
	 */
	private void findSinglesForChains() {
		mLogger.info("Finding potential singles for chain-link requirements, this might take a while...");

		for (final ReqsWithAttributes req : mListChainLinkReqs) {
			final List<ReqsWithAttributes> singles = mChainLinkSingles.computeIfAbsent(req, r -> new ArrayList<>());

			// Use a set to avoid duplicates if the same single is discovered via multiple variables
			final var seen = new java.util.LinkedHashSet<ReqsWithAttributes>();

			// Heuristic: singles that can matter typically share variables with the chain-link’s EC
			for (final TermVariable var : req.mFullExitCondition.getFreeVars()) {
				for (final ReqsWithAttributes other : mDictVar.getOrDefault(var, java.util.List.of())) {
					if (other != req && ChainLinkTest(req, other) && seen.add(other)
							&& (req.mOriginalPeaEventAutomata.getName() != other.mOriginalPeaEventAutomata.getName())) {
						singles.add(other);
					}
				}
			}
		}
	}

	/**
	 * Lightweight compatibility test between a chain-link and a single: - They must share at least one variable in
	 * their ECs (screening by intersection). - (Optionally) their “before-max” invariants must be mutually SAT when the
	 * penultimate bounds align.
	 */
	private boolean ChainLinkTest(final ReqsWithAttributes req1, final ReqsWithAttributes req2) {
		// Quickly discard if they do not reference a common variable
		if (!haveIntersection(req1.mFullExitCondition.getFreeVars(), req2.mFullExitCondition.getFreeVars())) {
			return false;
		}

		// Optional, more expensive check (currently gated by availability of before-max info)
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

	/** True iff the two variable arrays share at least one element (reference-equality by TermVariable). */
	public static boolean haveIntersection(final TermVariable[] vars1, final TermVariable[] variables) {
		for (final TermVariable elem : variables) {
			if (Arrays.asList(vars1).contains(elem)) {
				return true;
			}
		}
		return false;
	}

	// ================================================================================================================
	// Main search over chains (depth ≥ 1), then filling chains with singles
	// ================================================================================================================

	/**
	 * Explore chains of chain-links with increasing depth (1..mCombinationNum), restricted to friend relations, and try
	 * to complete each chain by adding singles that eliminate all remaining ECs. If at some depth no chains are
	 * possible, the search for larger depths stops early.
	 */
	private void rtiCheckChainLinkReqs() {
		if (mCombinationNum <= 0) {
			return; // nothing to do if requested depth is 0
		}

		for (int depth = 1; depth <= mCombinationNum; depth++) {
			mLogger.info("-------------- DEPTH (number of chain links) " + depth + " ------------------");

			final int maxSets = (int) nCk(mListChainLinkReqs.size(), depth);
			mLogger.info("   Max number of chains to check: " + maxSets);

			combinationsHelper = new ArrayList<>();

			// Build friend-only chains of the requested depth, starting from every chain-link as seed
			for (final ReqsWithAttributes req : mListChainLinkReqs) {
				final List<ReqsWithAttributes> friends = mChainLinkFriends.get(req);

				// If depth>1 but a node has no friends, it can never form a valid chain of that depth
				if (friends == null && depth > 1) {
					continue;
				}

				final List<ReqsWithAttributes> ChainSet = new ArrayList<>();
				ChainSet.add(req);
				findFriendChain(ChainSet, friends, depth);
			}

			mLogger.info("Number of chains found (friend-based skeletons): " + combinationsHelper.size());

			// Discard chains that cannot actually “dock” all links (i.e., do not form a true chain w.r.t. ECs + max)
			checkIfRealChainPossible();
			mLogger.info("Number of chains reduced to: " + combinationsHelper.size());

			if (combinationsHelper.isEmpty()) {
				// If no chains at current depth, larger depths will only be worse → stop early
				mLogger.info("No possible chains found for depth " + depth);
				long remainingSets = 0;
				for (int i = depth; i <= mCombinationNum; i++) {
					remainingSets += (int) nCk(mListChainLinkReqs.size(), i);
				}
				mLogger.info("Skipping " + remainingSets + " possible chains");
				return;
			}
			mLogger.info("Now trying to add singles to chains...");

			// For each chain skeleton, compute remaining ECs and attempt to eliminate them by adding singles
			for (final List<ReqsWithAttributes> combination : combinationsHelper) {
				LeftOverExitConditionsHelper = new ArrayList<>();

				// Compute “leftover” ECs: after docking chain-link A with chain-link B via a UNSAT pair,
				// remove that pair and carry forward the remaining ECs (e.g., [A,B] + [¬B,C] → remaining [A,C]).
				LeftOverEC(combination.get(0).mExitConditions, combination.subList(1, combination.size()));

				// Union of all prefiltered singles for chain members (unique)
				final List<ReqsWithAttributes> potentialSingles = new ArrayList<>();
				for (final ReqsWithAttributes req : combination) {
					final List<ReqsWithAttributes> singles = mChainLinkSingles.get(req);
					if (singles != null) {
						for (final ReqsWithAttributes single : singles) {
							if (!potentialSingles.contains(single) && !combination.contains(single)) {
								potentialSingles.add(single);
							}
						}
					}
				}

				mLogger.info(formatChainLog(combinationsHelper, combination, potentialSingles));

				helperCounter = 0;
				// For each variant of remaining ECs, try to eliminate them by (some subset of) singles
				for (final List<Term> leftOverEC : LeftOverExitConditionsHelper) {
					AddSinglesRecursive(leftOverEC, new ArrayList<>(), potentialSingles, combination);
				}

				mLogger.info("   " + helperCounter + " out of "
						+ (pow(2, potentialSingles.size()) * LeftOverExitConditionsHelper.size() - 1)
						+ " checks were needed.");
			}
		}
	}

	/**
	 * Compute the “leftover” EC lists after docking the first list of ECs with each following chain-link. Example:
	 * chain1 ECs: [A, B], chain2 ECs: [¬B, C] docking uses (B, ¬B) → remove those two; carry forward remaining [A, C].
	 * This routine enumerates all ways the docking could have happened, producing multiple leftover lists if needed.
	 */
	private void LeftOverEC(final List<Term> exitConditions, final List<ReqsWithAttributes> subList) {
		if (subList == null || subList.isEmpty()) {
			final List<Term> exitConditionsCopy = new ArrayList<>(exitConditions);
			exitConditionsCopy.sort(Comparator.comparing(Term::toString));
			LeftOverExitConditionsHelper.add(exitConditionsCopy);
			return; // base case: chain constructed
		}

		// Try all pairs (exitA, exitB) that are UNSAT → they can form the docking point
		for (final Term exitA : exitConditions) {
			for (final Term exitB : exitConditions) {
				final Term conj = SmtUtils.and(mScript, exitA, exitB);
				final LBool sat = SmtUtils.checkSatTerm(mScript, conj);
				if (sat != LBool.SAT) {
					final List<Term> newExitConditions = new ArrayList<>(exitConditions);
					newExitConditions.remove(exitA); // remove the used “A”
					newExitConditions.addAll(subList.get(0).mExitConditions); // add ECs of the next link
					newExitConditions.remove(exitB); // remove the used “B”

				}
			}
		}
	}

	/** Tiny integer power helper (avoids Math.pow double). */
	public static int pow(final int i, final int n) {
		int r = 1;
		for (int j = 0; j < n; j++) {
			r *= i;
		}
		return r;
	}

	/** Format a progress line for chain exploration, including number of potential singles and EC variants. */
	private String formatChainLog(final List<List<ReqsWithAttributes>> combinationsHelper1,
			final List<ReqsWithAttributes> combination, final List<ReqsWithAttributes> potentialSingles) {
		final StringBuilder sb = new StringBuilder();
		sb.append("   Check New Chain: ").append(combinationsHelper1.indexOf(combination)).append(" out of ")
				.append(combinationsHelper1.size()).append(" | Chain: [");

		for (final ReqsWithAttributes req : combination) {
			sb.append(req.mName).append(", ");
		}
		if (!combination.isEmpty()) {
			sb.setLength(sb.length() - 2);
		}
		sb.append("] | Potential Singles: ").append(potentialSingles.size());
		sb.append("] | Number of Different Chains: ").append(LeftOverExitConditionsHelper.size());
		sb.append(" - Therefore up to ")
				.append(pow(2, potentialSingles.size()) * LeftOverExitConditionsHelper.size() - 1)
				.append(" combinations to check");

		return sb.toString();
	}

	/**
	 * Depth-first try to add singles that eliminate leftover exit conditions. If a single does not reduce the EC set,
	 * skip it. If it removes some ECs, recurse on the reduced set with the remaining singles (to avoid permutations).
	 * If all ECs are eliminated, validate and record the RTI.
	 */
	public void AddSinglesRecursive(final List<Term> leftOverEC, final List<ReqsWithAttributes> singlesList,
			final List<ReqsWithAttributes> potentialSingles, final List<ReqsWithAttributes> chainLinks) {

		if (leftOverEC == null || leftOverEC.isEmpty()) {
			chainLinkRtiFoundCheck(singlesList, chainLinks);
			return;
		}
		for (int singleIndex = 0; singleIndex < potentialSingles.size(); singleIndex++) {
			final ReqsWithAttributes single = potentialSingles.get(singleIndex);
			final List<ReqsWithAttributes> newSinglesList = new ArrayList<>(singlesList);
			newSinglesList.add(single);

			final List<Term> newExitCondtitions = new ArrayList<>();
			helperCounter++;

			// Keep only those ECs that *still* survive when conjoined with the single’s EC
			for (final Term exitA : leftOverEC) {
				final Term conj = SmtUtils.and(mScript, exitA, single.mFullExitCondition);
				final LBool sat = SmtUtils.checkSatTerm(mScript, conj);
				if (sat != LBool.UNSAT) {
					newExitCondtitions.add(exitA);
				}
			}

			if (newExitCondtitions.isEmpty()) {
				// All ECs eliminated → we have a complete candidate (chain + selected singles)
				chainLinkRtiFoundCheck(chainLinks, newSinglesList);
			} else if (newExitCondtitions.size() < leftOverEC.size()) {
				// Only recurse if we made progress (reduced the EC set)
				final List<ReqsWithAttributes> newPotentialSingles =
						potentialSingles.subList(singleIndex + 1, potentialSingles.size());
				AddSinglesRecursive(newExitCondtitions, newSinglesList, newPotentialSingles, chainLinks);
			}
		}
	}

	/**
	 * Verify that friend-based chains actually can dock sequentially (EC pairing) and have SAT max-phase conjunction.
	 * Keeps only those chains that are feasible w.r.t. these two criteria.
	 */
	public void checkIfRealChainPossible() {
		final List<List<ReqsWithAttributes>> realChains = new ArrayList<>();

		for (final List<ReqsWithAttributes> combination : combinationsHelper) {
			final List<Term> exitConditions = combination.get(0).mExitConditions;

			// If combined max-phase invariants are UNSAT, we can discard this chain immediately
			if (!MaxPhaseSatCheck(combination)) {
				continue;
			}
			// Check the docking viability along the chain
			if (tryToFindChain(exitConditions, combination.subList(1, combination.size()))) {
				realChains.add(combination);
			}
		}
		combinationsHelper = realChains;
	}

	/**
	 * Recursive attempt to pair ECs along a chain. Returns true if we can eliminate two ECs at every step (i.e., always
	 * find UNSAT pairs to dock), thereby constructing a continuous chain.
	 */
	private boolean tryToFindChain(final List<Term> exitConditions, final List<ReqsWithAttributes> subList) {
		if (subList.isEmpty()) {
			return true; // base case: chain constructed
		}

		for (final Term exitA : exitConditions) {
			for (final Term exitB : exitConditions) {
				final Term conj = SmtUtils.and(mScript, exitA, exitB);
				final LBool sat = SmtUtils.checkSatTerm(mScript, conj);
				if (sat != LBool.SAT) {
					final List<Term> newExitConditions = new ArrayList<>(exitConditions);
					newExitConditions.remove(exitA);
					newExitConditions.addAll(subList.get(0).mExitConditions);
					newExitConditions.remove(exitB);

					if (subList.size() != 0 && newExitConditions.size() == 0) {
						final boolean found = tryToFindChain(newExitConditions, subList.subList(1, subList.size()));
						if (found) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	/**
	 * Build friend-only chains via DFS up to a given depth. This does *not* verify docking yet; it only builds
	 * combinations along the friend relation graph. Duplicates are canonicalized by sorting by name.
	 */
	private void findFriendChain(final List<ReqsWithAttributes> chainList, final List<ReqsWithAttributes> friends,
			final int depth) {
		if (chainList.size() == depth) {
			final List<ReqsWithAttributes> chainCopy = new ArrayList<>(chainList);
			chainCopy.sort(Comparator.comparing(ReqsWithAttributes::getName));
			if (!combinationsHelper.contains(chainCopy)) {
				combinationsHelper.add(chainCopy);
			}
			return;
		}

		if (friends == null) {
			return;
		}

		for (final ReqsWithAttributes friend : friends) {
			if (!chainList.contains(friend)) {
				final List<ReqsWithAttributes> chainListCopy = new ArrayList<>(chainList);
				chainListCopy.add(friend);
				final List<ReqsWithAttributes> friendFriends = mChainLinkFriends.get(friend);
				if (friendFriends != null) {
					findFriendChain(chainListCopy, friendFriends, depth);
				}
			}
		}
	}

	// Small helpers used during older exploration variants (kept for completeness)

	public List<ReqsWithAttributes> removeAt(final List<ReqsWithAttributes> list, final int index) {
		final List<ReqsWithAttributes> newList = new ArrayList<>(list);
		newList.remove(index);
		return newList;
	}

	public boolean tryToAddChainLink(final List<ReqsWithAttributes> remainingChainLinks,
			final List<Term> exitConditions, final int depth) {
		if (remainingChainLinks.isEmpty()) {
			return false;
		}
		if (depth == remainingChainLinks.size()) {
			return true;
		}

		for (int i = 0; i < remainingChainLinks.size(); i++) {
			for (final Term exitA : exitConditions) {
				for (final Term exitB : remainingChainLinks.get(i).mExitConditions) {
					final Term conj = SmtUtils.and(mScript, exitA, exitB);
					final LBool sat = SmtUtils.checkSatTerm(mScript, conj);

					if (sat != LBool.SAT) {
						final List<Term> newExitConditions = new ArrayList<>(exitConditions);
						newExitConditions.remove(exitA);
						newExitConditions.addAll(remainingChainLinks.get(i).mExitConditions);
						newExitConditions.remove(exitB);

						final List<ReqsWithAttributes> nextChain = new ArrayList<>(remainingChainLinks);
						nextChain.remove(i);

						final boolean result = tryToAddChainLink(nextChain, newExitConditions, depth);
						if (result) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	/** Conjoin all full ECs of a combination (used for quick checks). */
	public Term conjunctionExitConditions(final List<ReqsWithAttributes> combination) {
		Term conjunction = null;
		for (final ReqsWithAttributes req : combination) {
			conjunction = (conjunction == null) ? req.mFullExitCondition
					: SmtUtils.and(mScript, conjunction, req.mFullExitCondition);
		}
		return conjunction;
	}

	/** Return true iff the conjunction of all max-phase invariants in the combination is SAT. */
	public boolean MaxPhaseSatCheck(final List<ReqsWithAttributes> combination) {
		Term conjunction = null;
		for (final ReqsWithAttributes req : combination) {
			conjunction = (conjunction == null) ? req.mMaxPhase.mInvariant
					: SmtUtils.and(mScript, conjunction, req.mMaxPhase.mInvariant);
		}
		final LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		return result != LBool.UNSAT;
	}

	// Combinatorics helpers
	public static <T> List<List<T>> powerSet(final List<T> input, final int depth) {
		final List<List<T>> result = new ArrayList<>();
		backtrack(input, depth, 0, new ArrayList<>(), result);
		return result;
	}

	private static <T> void backtrack(final List<T> input, final int depth, final int start, final List<T> current,
			final List<List<T>> result) {
		if (current.size() == depth) {
			result.add(new ArrayList<>(current));
			return;
		}
		for (int i = start; i < input.size(); i++) {
			current.add(input.get(i));
			backtrack(input, depth, i + 1, current, result);
			current.remove(current.size() - 1);
		}
	}

	/** Compute n choose k (binomial coefficient) using an overflow-resistant iterative product. */
	public static long nCk(final int n, int k) {
		if (k < 0 || k > n) {
			return 0;
		}
		if (k == 0 || k == n) {
			return 1;
		}
		k = Math.min(k, n - k);
		long result = 1;
		for (int i = 1; i <= k; i++) {
			result = result * (n - i + 1) / i;
		}
		return result;
	}

	/**
	 * Validate a complete set (chain-links + chosen singles) as an RTI candidate: - Must include some timed requirement
	 * (otherwise it’s not a real-time issue). - Conjunction of all full ECs must be UNSAT (no way out). - Conjunction
	 * of all max-phase invariants must be SAT (feasible situation). If both hold and the set is minimal (not a superset
	 * of a previously found candidate), record it.
	 */
	private void chainLinkRtiFoundCheck(final List<ReqsWithAttributes> chainLinkRes,
			final List<ReqsWithAttributes> usedSingles) {

		// Minimality: if an earlier candidate is a subset of this, skip recording a superset
		for (final List<ReqsWithAttributes> rtiSet : mRTICombinations) {
			if (usedSingles.containsAll(rtiSet)) {
				mLogger.debug("set not minimal");
				return;
			}
		}

		final List<ReqsWithAttributes> fullSet = new ArrayList<>(chainLinkRes);
		fullSet.addAll(usedSingles);

		// Must be time-related
		boolean timedChecker = false;
		for (final ReqsWithAttributes r : fullSet) {
			if (r.mTimed) {
				timedChecker = true;
			}
		}
		if (!timedChecker) {
			mLogger.debug("set not timed");
			return;
		}

		// ECs must be mutually disjoint (UNSAT when conjoined)
		Term conjunction = fullSet.get(0).mFullExitCondition;
		for (int i = 1; i < fullSet.size(); i++) {
			conjunction = SmtUtils.and(mScript, conjunction, fullSet.get(i).mFullExitCondition);
		}
		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {
			mLogger.debug("set not disjoint");
			return;
		}

		// Max-phase invariants must be compatible (SAT)
		conjunction = fullSet.get(0).mMaxPhase.mInvariant;
		for (int i = 1; i < fullSet.size(); i++) {
			conjunction = SmtUtils.and(mScript, conjunction, fullSet.get(i).mMaxPhase.mInvariant);
		}
		result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result == LBool.UNSAT) {
			mLogger.debug("set not disjoint");
			return;
		}

		// We have a valid RTI candidate
		mLogger.debug("Rt-inconsistent set with chain-link found:");
		for (final ReqsWithAttributes r : fullSet) {
			mLogger.debug("   " + r.mName);
		}
		mRTICombinations.add(fullSet);
		mLogger.info("Rt-inconsistent set with chain-link found");
	}

	// ================================================================================================================
	// Debug term used to encode bounds (creates a numeric variable and reuses it in comparisons)
	// ================================================================================================================

	/** Create a numeric term variable “debugVar” used to translate phase bounds into SMT comparisons. */
	public void getDebugTerm() {
		// The actual logic here does not matter much; we only need a numeric sort compatible with bound constants.
		final Logics logic = Logics.QF_UFNIA;
		final Theory theo = new Theory(logic);
		final Term rhs = mScript.decimal(Double.toString(2.0));
		final Sort sort2 = rhs.getSort();
		mDebugVar = theo.createTermVariable("debugVar", sort2);
	}

	// ================================================================================================================
	// Singles-only precheck (pairwise)
	// ================================================================================================================

	/**
	 * For all variables, collect the singles that reference them and check all pairs: - EC conjunction must be UNSAT
	 * (disjoint exits), - max-phase invariants must be SAT (feasible together), - at least one of them is timed. Record
	 * any pairs that pass as RTI candidates.
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

				// canonicalize order to avoid duplicates
				final String k1 = a.getName();
				final String k2 = b.getName();
				final List<ReqsWithAttributes> canonicalPair =
						(k1.compareTo(k2) <= 0) ? java.util.List.of(a, b) : java.util.List.of(b, a);

				if (mRTICombinations.contains(canonicalPair)) {
					continue;
				}
				if (!a.mTimed && !b.mTimed) {
					continue;
				}

				if (rtiCheckFor2Reqs(a, b)) {
					mLogger.debug("RTI found for: " + a.mName + " and " + b.mName);
					mRTICombinations.add(canonicalPair);
				}
			}
		}
	}

	/**
	 * Pairwise RTI check for singles: 1) EC conjunction must be UNSAT (disjoint exits); 2) Max-phase invariants must be
	 * SAT; If both pass, the pair is a candidate (timedness is checked by the caller).
	 */
	private boolean rtiCheckFor2Reqs(final ReqsWithAttributes r1, final ReqsWithAttributes r2) {
		// 1) EC disjointness
		Term conj = SmtUtils.and(mScript, r1.mFullExitCondition, r2.mFullExitCondition);
		LBool res = SmtUtils.checkSatTerm(mScript, conj);
		if (res != LBool.UNSAT) {
			return false;
		}

		// 2) Max-phase compatibility
		if (r1.mMaxPhase == null || r2.mMaxPhase == null) {
			return false;
		}
		conj = SmtUtils.and(mScript, r1.mMaxPhase.mInvariant, r2.mMaxPhase.mInvariant);
		res = SmtUtils.checkSatTerm(mScript, conj);
		if (res == LBool.UNSAT) {
			return false;
		}

		return true;
	}

	/** All unordered pairs from a list (combinations of size 2). */
	public static List<List<ReqsWithAttributes>> combinations2(final List<ReqsWithAttributes> args) {
		final List<List<ReqsWithAttributes>> pairs = new ArrayList<>();
		for (int i = 0; i < args.size(); i++) {
			for (int j = i + 1; j < args.size(); j++) {
				pairs.add(Arrays.asList(args.get(i), args.get(j)));
			}
		}
		return pairs;
	}

	// ================================================================================================================
	// Attribute extraction (invariants, ECs, timing, seeping variants)
	// ================================================================================================================

	/**
	 * For each (CounterTrace, PEA) pair inside each requirement: - Build a ReqsWithAttributes view, - Extract
	 * penultimate/max phases, invariants, and time-bound encodings, - Compute full exit condition as
	 * DNF(not(penultimateInvariant)), - Classify into chain-link vs single; index singles by invariant variables, -
	 * Construct “seeping” variants by conjoining earlier invariants until seeping is blocked. The resulting objects
	 * populate mListChainLinkReqs (for chain-links and seeped variants) and mDictVar (for singles).
	 */
	private void getAttributes(final List<ReqPeas> reqPeas) {
		for (final ReqPeas reqPea : reqPeas) {
			for (final Map.Entry<CounterTrace, PhaseEventAutomata> child : reqPea.getCounterTrace2Pea()) {

				final CounterTrace ct = child.getKey();
				final PhaseEventAutomata pea = child.getValue();
				final DCPhase[] phases = ct.getPhases();
				final int n = phases.length;

				if (n < 2) {
					mLogger.warn("CounterTrace too short ({} phases) for {}", n, pea.getName());
					continue;
				}

				final ReqsWithAttributes req = new ReqsWithAttributes(reqPea);
				req.mName = pea.getName();
				req.mOriginalPeaEventAutomata = pea;
				req.mCounterTrace = ct;

				// Timed if the automaton uses clocks
				req.mTimed = (pea.getClocks().size() > 0);

				// Penultimate phase (always exists here)
				final DCPhase penultDC = phases[n - 2];
				req.mPenultimatePhase = new Phase(penultDC);
				req.mPenultimatePhase.mInvariant = mCddToSmt.toSmt(penultDC.getInvariant());
				req.mPenultimatePhase.mInvariantVar = req.mPenultimatePhase.mInvariant.getFreeVars();
				req.mPenultimatePhase.mBound = boundToSmt(req.mPenultimatePhase);

				// Full exit condition = DNF(¬penultInvariant)
				final Term negInv = SmtUtils.not(mScript, req.mPenultimatePhase.mInvariant);
				req.mFullExitCondition = SmtUtils.toDnf(mServices, mManagedScript, negInv);
				req.mExitConditions = new ArrayList<>(Arrays.asList(SmtUtils.getDisjuncts(req.mFullExitCondition)));

				// Choose max phase: if penultimate has a bound, use it as "max"; otherwise take n-3
				final boolean penultHasBound = penultDC.getBoundType() != 0;
				final int maxIdxFromEnd = penultHasBound ? 2 : 3;

				mListAllReqs.add(req);
				// Classify chain-link vs single + index singles by variables
				if (req.mExitConditions.size() > 1) {
					req.mChainLinkReq = true;
					mListChainLinkReqs.add(req);
				} else {
					final TermVariable[] vars = req.mPenultimatePhase.mInvariantVar;
					if (vars != null) {
						for (final Term v : vars) {
							mDictVar.computeIfAbsent((TermVariable) v, k -> new ArrayList<>()).add(req);
						}
					}
				}

				// Guard against short traces
				if (n - maxIdxFromEnd < 0) {
					mLogger.warn("Cannot determine max phase");
					continue;
				}
				req.mMaxPhase = new Phase(phases[n - maxIdxFromEnd]);
				req.mMaxPhase.mInvariant = mCddToSmt.toSmt(req.mMaxPhase.mDCPhase.getInvariant());
				req.mMaxPhase.mInvariantVar = req.mMaxPhase.mInvariant.getFreeVars();
				req.mMaxPhase.mBound = boundToSmt(req.mMaxPhase);

				// --- Seeping variants ---
				// Build cumulative “seep” invariants walking backwards as long as seeping is allowed (both time/obs).
				final record SeepInvariant(DCPhase maxPhase, Term invariant) {
				}
				final List<SeepInvariant> seepInvariants = new ArrayList<>();
				seepInvariants.add(new SeepInvariant(n - 3 >= 0 ? phases[n - 3] : null,
						mCddToSmt.toSmt(phases[n - 2].getInvariant())));

				for (int i = n - 3; i >= 0; i--) {
					final DCPhase phase = phases[i];
					final DCPhase maxPhase = i - 1 >= 0 ? phases[i - 1] : null;
					final Term term = mCddToSmt.toSmt(phases[i].getInvariant());
					final Term seepInvariant = SmtUtils.and(mScript, seepInvariants.getLast().invariant, term);

					// Stop if the first phase is TRUE (no further restriction) → nothing more to seep
					if (i == 0 && phase.getInvariant() == CDD.TRUE) {
						break;
					}

					// Stop if time-seep not possible: “≥” type bounds break the forward accumulation
					if (phase.getBoundType() == CounterTrace.BOUND_GREATER
							|| phase.getBoundType() == CounterTrace.BOUND_GREATEREQUAL) {
						break;
					}

					// Stop if observationally UNSAT to keep only feasible seep chains
					if (SmtUtils.checkSatTerm(mScript, seepInvariant) == LBool.UNSAT) {
						break;
					}

					// Add unique seep step (avoid duplicates by equivalence)
					if (SmtUtils.checkEquivalence(seepInvariant, seepInvariants.getLast().invariant,
							mScript) != LBool.UNSAT
							|| maxPhase != null && SmtUtils.checkEquivalence(mCddToSmt.toSmt(maxPhase.getInvariant()),
									mCddToSmt.toSmt(seepInvariants.getLast().maxPhase.getInvariant()),
									mScript) != LBool.UNSAT) {
						seepInvariants.add(new SeepInvariant(maxPhase, seepInvariant));
					}
				}

				// For each seep step, create a synthetic chain-link whose EC is DNF(¬seepInvariant).
				for (int i = 1; i < seepInvariants.size(); i++) {
					final Term negation = SmtUtils.not(mScript, seepInvariants.get(i).invariant);
					final Term fullExitCondition = SmtUtils.toDnf(mServices, mManagedScript, negation);

					final ReqsWithAttributes seepReq = new ReqsWithAttributes(req);
					seepReq.mName = seepReq.mName + "_SEEPING_" + i;
					seepReq.mFullExitCondition = fullExitCondition;
					seepReq.mExitConditions =
							new ArrayList<>(Arrays.asList(SmtUtils.getDisjuncts(seepReq.mFullExitCondition)));

					if (seepInvariants.get(i).maxPhase != null) {
						seepReq.mMaxPhase = new Phase(seepInvariants.get(i).maxPhase);
						seepReq.mMaxPhase.mInvariant = mCddToSmt.toSmt(seepReq.mMaxPhase.mDCPhase.getInvariant());
						seepReq.mMaxPhase.mInvariantVar = seepReq.mMaxPhase.mInvariant.getFreeVars();
						seepReq.mMaxPhase.mBound = boundToSmt(seepReq.mMaxPhase);
					} else {
						seepReq.mMaxPhase = null;
					}

					seepReq.mChainLinkReq = true;
					mListChainLinkReqs.add(seepReq);
					mListAllReqs.add(seepReq);
				}
			}
		}
	}

	// ================================================================================================================
	// Formatting / utilities
	// ================================================================================================================

	/** Map internal candidates back to (PatternType, PEA) entries for downstream checking. */
	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(final List<ReqsWithAttributes> reqs) {
		return reqs.stream()
				.map(req -> new AbstractMap.SimpleEntry<>(req.mOriginalPea.getPattern(), req.mOriginalPeaEventAutomata))
				.sorted(Comparator.comparing(Entry::getValue)).toArray(Entry[]::new);
	}

	/**
	 * Translate a phase’s bound into an SMT inequality over the shared debugVar. This permits easy
	 * equality/compatibility checks among different phases’ time constraints.
	 */
	private Term boundToSmt(final Phase phase) {
		final int bt = phase.mDCPhase.getBoundType();
		if (bt == 0) {
			return mScript.term("true"); // no bound
		}

		final Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
		switch (bt) {
		case 2:
			return SmtUtils.greater(mScript, mDebugVar, rhs); // >
		case 1:
			return SmtUtils.geq(mScript, mDebugVar, rhs); // ≥
		case -2:
			return SmtUtils.less(mScript, mDebugVar, rhs); // <
		default:
			return SmtUtils.leq(mScript, mDebugVar, rhs); // ≤ (covers -1 and others)
		}
	}
}
