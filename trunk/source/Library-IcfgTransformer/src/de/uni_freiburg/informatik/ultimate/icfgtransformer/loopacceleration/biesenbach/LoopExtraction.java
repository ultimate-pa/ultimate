package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.AbstractMap;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class LoopExtraction<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation> {

	private final ILogger mLogger;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final ManagedScript mMgScript;
	private final Deque<SimpleLoop> mLoops;
	private final List<INLOC> mLoopHeads;

	public LoopExtraction(final ILogger logger, final IIcfg<INLOC> originalIcfg) {

		// Setup
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		final CfgSmtToolkit mCfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = mCfgSmtToolkit.getManagedScript();
		mLoops = new ArrayDeque<>();
		mLoopHeads = getLoopHeads();

		for (final INLOC loopHead : mLoopHeads) {
			final Deque<IcfgEdge> path = getLoopPath(loopHead);
			if (path.isEmpty()) {
				continue;
			}
			final List<Entry<UnmodifiableTransFormula, IcfgLocation>> exitEdges = findAllExits(loopHead, path);
			final UnmodifiableTransFormula pathTransformula = pathToTransformula(path);
			// check if loop has values to accelerate
			if (!pathTransformula.getAssignedVars().isEmpty()) {
				mLoops.addLast(new SimpleLoop(pathTransformula, loopHead, exitEdges));
			}
		}
	}

	private List<Entry<UnmodifiableTransFormula, IcfgLocation>> findAllExits(final INLOC loopHead,
			final Deque<IcfgEdge> path) {
		final List<Entry<UnmodifiableTransFormula, IcfgLocation>> exitEdges = new ArrayList<>();
		for (final IcfgEdge edge : loopHead.getOutgoingEdges()) {
			if (!edge.getTransformula().equals(path.getFirst().getTransformula())) {
				final Entry<UnmodifiableTransFormula, IcfgLocation> entry = new AbstractMap.SimpleEntry<>(
						Tools.negateUnmodifiableTransFormula(mMgScript, edge.getTransformula()), edge.getTarget());
				exitEdges.add(entry);
			}
		}
		final Deque<IcfgEdge> pathCopy = Tools.cloneDeque(path);
		pathCopy.removeLast();
		final Deque<IcfgEdge> exitPath = new ArrayDeque<>();
		while (!pathCopy.isEmpty()) {
			final IcfgEdge nextEdge = pathCopy.pop();
			for (final IcfgEdge outgoingEdge : nextEdge.getTarget().getOutgoingEdges()) {
				if (!path.contains(outgoingEdge)) {
					Entry<UnmodifiableTransFormula, IcfgLocation> entry;
					if (!exitPath.isEmpty()) {
						final Deque<IcfgEdge> exit = Tools.cloneDeque(exitPath);
						final UnmodifiableTransFormula pathFormula = pathToTransformula(exit);
						final UnmodifiableTransFormula exitPathFormula = instertFormula(
								Tools.negateUnmodifiableTransFormula(mMgScript, outgoingEdge.getTransformula()),
								pathFormula);
						// UnmodifiableTransFormula exitPathFormula = joinTransFormula(pathFormula,
						// Tools.negateUnmodifiableTransFormula(mMgScript, outgoingEdge.getTransformula()));
						entry = new AbstractMap.SimpleEntry<>(exitPathFormula, outgoingEdge.getTarget());
					} else {
						entry = new AbstractMap.SimpleEntry<>(
								Tools.negateUnmodifiableTransFormula(mMgScript, outgoingEdge.getTransformula()),
								outgoingEdge.getTarget());
					}
					exitEdges.add(entry);
				} else {
					exitPath.add(outgoingEdge);
				}
			}
		}
		return exitEdges;
	}

	private UnmodifiableTransFormula instertFormula(final UnmodifiableTransFormula mainFormula,
			final UnmodifiableTransFormula substituteFormula) {
		final Script script = mMgScript.getScript();
		final Map<Term, Term> substitute = new HashMap<>();
		for (final IProgramVar var : mainFormula.getInVars().keySet()) {
			if (substituteFormula.getOutVars().containsKey(var)) {
				final Term value = script.term("+", substituteFormula.getInVars().values().iterator().next(),
						Rational.ONE.toTerm(script.sort("Int")));
				substitute.put(mainFormula.getInVars().get(var), value);
			}
		}
		final Substitution sub = new Substitution(mMgScript, substitute);
		final Term transformedExitFormula = sub.transform(mainFormula.getFormula());

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(substituteFormula.getInVars(), substituteFormula.getInVars(), false,
						mainFormula.getNonTheoryConsts(), true, mainFormula.getBranchEncoders(), true);
		tfb.setFormula(transformedExitFormula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		tfb.finishConstruction(mMgScript);
		final UnmodifiableTransFormula finalFormula = tfb.finishConstruction(mMgScript);

		// produce sequential composition
		// final List<UnmodifiableTransFormula> transFormulas = null;
		// final IUltimateServiceProvider services = null;
		// final UnmodifiableTransFormula seqComp = TransFormulaUtils.sequentialComposition(mLogger, services,
		// mMgScript,
		// true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
		// SimplificationTechnique.SIMPLIFY_DDA, transFormulas);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("-------------------------");
			mLogger.debug("mainFormula : " + mainFormula);
			mLogger.debug("substituteFormula : " + substituteFormula);
			mLogger.debug("subsitute : " + substitute);
			mLogger.debug("finalFormula : " + finalFormula);
			mLogger.debug("-------------------------");
		}
		return finalFormula;
	}

	public Deque<SimpleLoop> getLoopTransFormulas() {
		return mLoops;
	}

	@SuppressWarnings("unchecked")
	private Deque<IcfgEdge> getLoopPath(final INLOC loopHead) {
		// final Deque to return
		Deque<IcfgEdge> loopPath = new ArrayDeque<>();
		// locations to check (starting from loopHead)
		final Deque<INLOC> openLocations = new ArrayDeque<>();
		openLocations.addFirst(loopHead);
		// locations marked
		final List<INLOC> markedLocations = new ArrayList<>();
		markedLocations.add(loopHead);
		// remember the path
		final Map<IcfgLocation, Deque<IcfgEdge>> paths = new HashMap<>();
		paths.put(loopHead, new ArrayDeque<>());
		// while there are open locations
		while (!openLocations.isEmpty()) {
			final INLOC location = openLocations.removeFirst();
			// go throw every edge
			for (final IcfgEdge edge : location.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				// first loop-path found
				if (mLoopHeads.contains(target) && !target.equals(loopHead)) {
					continue;
				} else if (target.equals(loopHead) && loopPath.isEmpty()) {
					paths.get(location).addLast(edge);
					loopPath = paths.get(location);
				} else if (target.equals(loopHead) && markedLocations.contains(target)) {
					return new ArrayDeque<>();
				} else {
					markedLocations.add((INLOC) target);
					openLocations.addLast((INLOC) target);
					final Deque<IcfgEdge> clone = Tools.cloneDeque(paths.get(location));
					clone.addLast(edge);
					paths.put(target, clone);
				}
			}
		}
		return loopPath;
	}

	private UnmodifiableTransFormula pathToTransformula(final Deque<IcfgEdge> path) {
		if (path.size() == 1) {
			return path.getFirst().getTransformula();
		} else {
			UnmodifiableTransFormula transformula =
					joinTransFormula(path.removeFirst().getTransformula(), path.removeFirst().getTransformula());
			for (final IcfgEdge edge : path) {
				transformula = joinTransFormula(transformula, edge.getTransformula());
			}
			return transformula;
		}
	}

	private UnmodifiableTransFormula joinTransFormula(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
		final Map<Term, Term> substitute = new HashMap<>();
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>(first.getInVars());
		for (final Entry<IProgramVar, TermVariable> inVar : second.getInVars().entrySet()) {
			if (!inVars.containsKey(inVar.getKey())) {
				inVars.put(inVar.getKey(), inVar.getValue());
			}
		}
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>(second.getOutVars());
		for (final Entry<IProgramVar, TermVariable> outVar : first.getOutVars().entrySet()) {
			if (!outVars.containsKey(outVar.getKey())) {
				outVars.put(outVar.getKey(), outVar.getValue());
			}
		}
		for (final IProgramVar var : first.getOutVars().keySet()) {
			if (second.getInVars().containsKey(var)) {
				substitute.put(second.getInVars().get(var), first.getOutVars().get(var));
				if (second.getInVars().get(var).equals(second.getOutVars().get(var))) {
					outVars.put(var, first.getOutVars().get(var));
				}
			}
		}
		final Set<IProgramConst> nonTheoryConsts = new HashSet<>();
		nonTheoryConsts.addAll(first.getNonTheoryConsts());
		nonTheoryConsts.addAll(second.getNonTheoryConsts());
		final Substitution sub = new Substitution(mMgScript, substitute);
		final Term transformedSecond = sub.transform(second.getFormula());
		final Term jointFormula = mMgScript.getScript().term("and", first.getFormula(), transformedSecond);

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(inVars, outVars, false, nonTheoryConsts, true, null, false);
		tfb.setFormula(jointFormula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mMgScript);
	}

	@SuppressWarnings("unchecked")
	private List<INLOC> getLoopHeads() {
		// TODO how can I guaranty to pick the right LoopHead
		// Example: ambigousLoopEntry - L13loopEntry vs L14

		final List<INLOC> loopHeads = new ArrayList<>();
		final Set<INLOC> markedNodes = new HashSet<>();
		final List<INLOC> openNodes = new ArrayList<>(mOriginalIcfg.getInitialNodes());

		while (!openNodes.isEmpty()) {
			final INLOC openNode = openNodes.remove(0);
			if (markedNodes.contains(openNode)) {
				loopHeads.add(openNode);
			} else {
				openNode.getOutgoingEdges().forEach(edge -> {
					if (!openNodes.contains(edge.getTarget())) {
						openNodes.add((INLOC) edge.getTarget());
					}
				});
			}
			markedNodes.add(openNode);
		}
		return loopHeads;
	}
}
