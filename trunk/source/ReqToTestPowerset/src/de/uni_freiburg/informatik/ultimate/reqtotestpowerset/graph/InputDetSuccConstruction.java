package de.uni_freiburg.informatik.ultimate.reqtotestpowerset.graph;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;

public class InputDetSuccConstruction {
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final GuardGraph mGuardGraph;
	private final Set<GuardGraph> mSeenNodes;
	private final LinkedList<GuardGraph> mQueue;
	private final Set<Term> mMonomials;
	private final Set<Term> mOutputVars;
	private final Sort mSort;
	private final Set<GuardGraph> mAutStates;
	private Term mTrue;
	private Term mFalse;
	private final SearchGraphTable mSGTable;

	public InputDetSuccConstruction(final ManagedScript managedScript, final IUltimateServiceProvider services,
			final ILogger logger, final GuardGraph powersetAuto, final Script script,
			final Req2TestReqSymbolTable symboltable) {
		mManagedScript = managedScript;
		mServices = services;
		mLogger = logger;
		mScript = script;
		mSeenNodes = new HashSet<>();
		mQueue = new LinkedList<>();
		mAutStates = new HashSet<>();
		mSort = mScript.sort("Bool");
		mMonomials = createMonomials(symboltable);
		mOutputVars = getOutputVariables(symboltable.getOutputVars());
		makeTrueAndFalse();
		mGuardGraph = constructInputDetSuccAutomaton(powersetAuto);
		mSGTable = new SearchGraphTable(logger, script);
		populateSearchGraph();
		mLogger.warn(mSGTable);
		mSGTable.makeTests();
		mLogger.warn(mSGTable.getNrOfFinals());
		mLogger.warn(mSGTable.getNrOfTests());
	}

	private void makeTrueAndFalse() {
		for (final Term t : mMonomials) {
			final Term nt = SmtUtils.not(mScript, t);
			mFalse = SmtUtils.and(mScript, t, nt);
			mTrue = SmtUtils.or(mScript, t, nt);
			break;
		}
	}

	private Set<Term> getOutputVariables(final Set<String> inputVars) {
		final Set<Term> result = new HashSet<>();
		for (final String varname : inputVars) {
			final Term a = mScript.variable(varname, mSort);
			final Term na = SmtUtils.not(mScript, a);
			result.add(a);
			result.add(na);
		}
		return result;
	}

	// inputvar I : {Term I, Term notI}
	private HashMap<String, Set<Term>> inVarToTermMap(final Set<String> inVars) {
		final HashMap<String, Set<Term>> result = new HashMap<>();
		for (final String varname : inVars) {
			final Term a = mScript.variable(varname, mSort);
			final Term na = SmtUtils.not(mScript, a);
			final Set<Term> values = new HashSet<>();
			values.add(a);
			values.add(na);
			result.put(varname, values);
		}
		return result;
	}

	// mon1 : I and J and ....
	private Set<Term> createMonomials(final Req2TestReqSymbolTable sbt) {
		final HashMap<String, Set<Term>> inVarToTerms = inVarToTermMap(sbt.getInputVars());
		Set<Term> result = new HashSet<>();
		Set<Term> oldRes = new HashSet<>();

		// get one key as first element to create the first monomials (length 1)
		// e.g. mon0 will be I and mon1 will be not I
		for (final String key : inVarToTerms.keySet()) {
			result.addAll(inVarToTerms.get(key));
			inVarToTerms.remove(key);
			oldRes = new HashSet<>(result);
			break;
		}

		// now for the rest of the input Terms
		if (!inVarToTerms.isEmpty()) {
			for (final String key : inVarToTerms.keySet()) {
				result = new HashSet<>();
				for (final Term boolInputVal : inVarToTerms.get(key)) {
					for (final Term oldMonKey : oldRes) {
						result.add(SmtUtils.and(mScript, boolInputVal, oldMonKey));
					}
				}
				oldRes = new HashSet<>(result);
			}
		}
		return result;
	}

	public GuardGraph getAutomaton() {
		return mGuardGraph;
	}

	// calculate the successors here
	private Set<GuardGraph> findSuccessors(final GuardGraph givenNode, final Term givenMonomial) {
		final Set<GuardGraph> result = new HashSet<>();

		for (final GuardGraph neighbour : givenNode.getOutgoingNodes()) {
			if (!(givenNode.getOutgoingEdgeLabel(neighbour) == null) && !SmtUtils
					.isFalseLiteral(SmtUtils.and(mScript, givenNode.getOutgoingEdgeLabel(neighbour), givenMonomial))) {
				result.add(neighbour);
			}
		}
		return result;
	}

	private GuardGraph collectionContains(final Collection<GuardGraph> collection, final GuardGraph thisInpDetANode) {
		for (final GuardGraph gg : collection) {
			if (gg.isSameNode(thisInpDetANode)) {
				return gg;
			}
		}
		return null;
	}

	private GuardGraph constructInputDetSuccAutomaton(final GuardGraph productAutomaton) {
		final Set<GuardGraph> initialIndex = new HashSet<>();
		initialIndex.add(productAutomaton);
		final GuardGraph initialPowerNode = new GuardGraph(0, new HashSet<>(initialIndex));
		mAutStates.add(initialPowerNode);
		int newlabel = 1;
		// add it to queue
		mQueue.add(initialPowerNode);

		// now go over the queue
		while (mQueue.size() > 0) {

			final GuardGraph thisInpDetANode = mQueue.pop();
			mSeenNodes.add(thisInpDetANode);

			for (final Term mon : mMonomials) {
				final Set<GuardGraph> succsrs = getAllSuccessors(thisInpDetANode.getBuildingNodes(), mon);

				GuardGraph targetNode = new GuardGraph(newlabel, succsrs);
				// TODO: refactor! take HashMap<set<GuardGraph>, GuardGraph> which stores the internal nodes i.e.
				// succsrs and indexes nodes
				// accordingly.
				if (collectionContains(mAutStates, targetNode) == null) {
					mAutStates.add(targetNode);
				} else {
					targetNode = collectionContains(mAutStates, targetNode);
				}

				final Term edgelabel = getNewEdgeLabel(thisInpDetANode.getBuildingNodes(), succsrs, mon);

				if (collectionContains(mQueue, targetNode) == null
						&& collectionContains(mSeenNodes, targetNode) == null) {
					mQueue.add(targetNode);
					newlabel++;
				}

				if (thisInpDetANode.getOutgoingNodes().contains(targetNode)) {
					final Term newLabel =
							SmtUtils.or(mScript, thisInpDetANode.getOutgoingEdgeLabel(targetNode), edgelabel);
					thisInpDetANode.disconnectOutgoing(targetNode);
					thisInpDetANode.connectOutgoing(targetNode, newLabel);
					initialPowerNode.incEdges();

				} else {
					thisInpDetANode.connectOutgoing(targetNode, edgelabel);
					initialPowerNode.incEdges();
				}

			}
		}
		return initialPowerNode;
	}

	private Set<GuardGraph> getAllSuccessors(final Set<GuardGraph> buildingNodes, final Term monomial) {
		final Set<GuardGraph> result = new HashSet<>();
		for (final GuardGraph buildingNode : buildingNodes) {
			result.addAll(findSuccessors(buildingNode, monomial));
		}
		return result;
	}

	private Term getNewEdgeLabel(final Set<GuardGraph> buildingNodes, final Set<GuardGraph> successors,
			final Term monomial) {
		// hack to create a false term for the later disjunction
		final LinkedList<Term> termsOfDisjunction = new LinkedList<>();
		for (final GuardGraph fromNode : buildingNodes) {
			for (final GuardGraph toNode : successors) {
				if (fromNode.getSuccessors().contains(toNode)) {
					final Term oldLabelToSuccessor = fromNode.getOutgoingEdgeLabel(toNode);
					final Term newLabelToSuccessor = SmtUtils.and(mScript, oldLabelToSuccessor, monomial);
					termsOfDisjunction.add(newLabelToSuccessor);
				}
			}
		}
		return makeDisj(outputTester(termsOfDisjunction));
	}

	/***
	 * Method test if any one output variable is present in each disjunction term Method removes output variables from
	 * disjunction terms if said output variable is not present in all the disjunction terms
	 *
	 * @param disjTermToBeTested
	 *            Term may or may not contain Output variables
	 * @return testedTerm Term contains the same output variable in all its disjuncs or none at all
	 */
	private LinkedList<Term> outputTester(final LinkedList<Term> termsToTest) {
		LinkedList<Term> localList = new LinkedList<>(termsToTest);
		final Set<Term> oVarHelper = findOutputVars(termsToTest);

		if (oVarHelper.size() == 0) {
			return termsToTest;
		} else {
			for (final Term ov : oVarHelper) {
				if (testTermsContainOVar(localList, ov)) {
					continue;
				} else {
					localList = removeOVar(localList, ov);
				}
			}
			return localList;
		}
	}

	private LinkedList<Term> removeOVar(final LinkedList<Term> localList, final Term ov) {
		final LinkedList<Term> helperList = new LinkedList<>();
		for (final Term t : localList) {
			helperList.add(remakeTerm(t, ov));
		}
		return helperList;
	}

	private boolean testTermsContainOVar(final List<Term> disjTerms, final Term ov) {
		for (final Term disjTerm : disjTerms) {
			boolean disjTermFlag = false;
			for (final Term element : SmtUtils.getConjuncts(disjTerm)) {
				if (element.equals(ov)) {
					disjTermFlag = true;
				}
			}
			if (!disjTermFlag) {
				return false;
			}
		}
		return true;
	}

	// TODO this will not work if termToRemake is not a conjunction, I think
	// or a conjunction of conjunctions...
	private Term remakeTerm(final Term termToRemake, final Term oVar) {
		Term result = mTrue;
		final Term dnf = SmtUtils.toDnf(mServices, mManagedScript, termToRemake);
		for (final Term disjTerm : SmtUtils.getDisjuncts(dnf)) {
			for (final Term element : SmtUtils.getConjuncts(disjTerm)) {
				if (!element.equals(oVar)) {
					result = SmtUtils.and(mScript, result, element);
				}
			}
		}
		return result;
	}

	private Set<Term> findOutputVars(final LinkedList<Term> termsToTest) {
		final Set<Term> result = new HashSet<>();
		for (final Term element : termsToTest) {
			// find terms which are output variables
			for (final Term x : element.getFreeVars()) {
				for (final Term o : mOutputVars) {
					if (x.equals(o)) {
						result.add(x);
					}
				}
			}
		}
		return result;
	}

	private Term makeDisj(final LinkedList<Term> terms) {
		Term result = mFalse;
		for (final Term t : terms) {
			result = SmtUtils.or(mScript, result, t);
		}
		return result;
	}

	public void populateSearchGraph() {
		final LinkedList<GuardGraph> open = new LinkedList<>();
		final Set<GuardGraph> seen = new HashSet<>();

		mSGTable.add(mGuardGraph, 0, null, false);
		open.add(mGuardGraph);

		while (open.size() > 0) {
			final GuardGraph workingNode = open.pop();
			seen.add(workingNode);

			for (final GuardGraph successor : workingNode.getOutgoingNodes()) {
				mSGTable.add(successor, mSGTable.getDistOfElement(workingNode) + 1, workingNode, isEndNode(successor));
				if (!seen.contains(successor) && !open.contains(successor)) {
					open.add(successor);
				}
			}
		}
	}

	private boolean isEndNode(final GuardGraph node) {
		boolean localFlag = false;
		for (final Term oVar : mOutputVars) {
			for (final GuardGraph succ : node.getOutgoingNodes()) {
				final Term[] disjs = SmtUtils
						.getDisjuncts(SmtUtils.toDnf(mServices, mManagedScript, node.getOutgoingEdgeLabel(succ)));

				localFlag = localFlag || testTermsContainOVar(Arrays.asList(disjs), oVar);
			}
		}
		return localFlag;
	}
}
