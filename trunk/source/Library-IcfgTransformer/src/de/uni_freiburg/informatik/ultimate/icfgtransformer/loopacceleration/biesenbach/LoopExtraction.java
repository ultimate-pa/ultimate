package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class LoopExtraction <INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>{
	
	private final ILogger mLogger;
	private final IIcfg<INLOC> mOriginalIcfg;
	private final Class<OUTLOC> mOutLocationClass;
	private final ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	private final String mNewIcfgIdentifier;
	private final ITransformulaTransformer mTransformer;
	private final IBacktranslationTracker mBacktranslationTracker;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgScript;
	private final Deque<SimpleLoop> mLoops;

	public LoopExtraction(final ILogger logger, final IIcfg<INLOC> originalIcfg, final Class<OUTLOC> outLocationClass,
			final ILocationFactory<INLOC, OUTLOC> funLocFac, final String newIcfgIdentifier,
			final ITransformulaTransformer transformer, final IBacktranslationTracker backtranslationTracker,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mOutLocationClass = outLocationClass;
		mFunLocFac = funLocFac;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mTransformer = transformer;
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;
		final CfgSmtToolkit mCfgSmtToolkit = originalIcfg.getCfgSmtToolkit();
		mMgScript = mCfgSmtToolkit.getManagedScript();
		mLoops = new ArrayDeque<>();
		List<INLOC> loopHeads = getLoopHeads();
		for(INLOC loopHead : loopHeads){
			Deque<IcfgEdge> path = getLoopPath(loopHead);
			List<IcfgEdge> exitEdges = loopHead.getOutgoingEdges();
			exitEdges.remove(path.getFirst());
			mLoops.addLast(new SimpleLoop(pathToTransformula(path), loopHead, exitEdges));
		}
	}
	
	public Deque<SimpleLoop> getLoopTransFormulas(){
		return mLoops;
	}
	
	@SuppressWarnings("unchecked")
	private Deque<IcfgEdge> getLoopPath(INLOC loopHead) {
		Deque<IcfgEdge> loopPath = new ArrayDeque<>();
		Deque<INLOC> openLocations = new ArrayDeque<>();
		openLocations.addFirst(loopHead);
		List<INLOC> markedLocations = new ArrayList<>();
		markedLocations.add(loopHead);
		Map<IcfgLocation, Deque<IcfgEdge>> paths = new HashMap<>();
		paths.put(loopHead, new ArrayDeque<>());
		while(!openLocations.isEmpty()){
			INLOC location = openLocations.removeFirst();
			for(IcfgEdge edge : location.getOutgoingEdges()){
				if(edge.getTarget().equals(loopHead) && loopPath.isEmpty()){
					paths.get(location).addLast(edge);
					loopPath = paths.get(location);
				}else if(edge.getTarget().equals(loopHead)){
					return new ArrayDeque<>();
				}else if(!markedLocations.contains(edge.getTarget())){
					markedLocations.add((INLOC) edge.getTarget());
					openLocations.addLast((INLOC) edge.getTarget());
					Deque<IcfgEdge> clone = cloneDeque(paths.get(location));
					clone.addLast(edge);
					paths.put(edge.getTarget(), clone);
				}
			}
		}
		return loopPath;
	}
	
	private Deque<IcfgEdge> cloneDeque(Deque<IcfgEdge> deque){
		Deque<IcfgEdge> clone = new ArrayDeque<>();
		for(IcfgEdge edge : deque){
			clone.add(edge);
		}
		return clone;
	}
	
	private UnmodifiableTransFormula pathToTransformula(Deque<IcfgEdge> path){
		if(path.isEmpty()){
			return null;
		}else if(path.size() == 1){
			return path.getFirst().getTransformula();
		}else{
			UnmodifiableTransFormula transformula = joinTransFormula(path.removeFirst().getTransformula(), path.removeFirst().getTransformula());
			for(IcfgEdge edge : path){
				transformula = joinTransFormula(transformula, edge.getTransformula());
			}
			return transformula;
		}
	}
	
	private UnmodifiableTransFormula joinTransFormula(UnmodifiableTransFormula first, UnmodifiableTransFormula second){
		final Map<Term, Term> substitute = new HashMap<>();
		final Map<IProgramVar, TermVariable> inVars = new HashMap<>(first.getInVars());
		for(Entry<IProgramVar, TermVariable> inVar : second.getInVars().entrySet()){
			if(!inVars.containsKey(inVar.getKey())){
				inVars.put(inVar.getKey(),inVar.getValue());
			}
		}
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>(second.getOutVars());
		for(Entry<IProgramVar, TermVariable> outVar : first.getOutVars().entrySet()){
			if(!outVars.containsKey(outVar.getKey())){
				outVars.put(outVar.getKey(),outVar.getValue());
			}
		}
		for (final IProgramVar var : first.getOutVars().keySet()) {
			if (second.getInVars().containsKey(var)) {
				substitute.put(second.getInVars().get(var), first.getOutVars().get(var));
			}
		}

		Set<IProgramConst> nonTheoryConsts = new HashSet<>();
		nonTheoryConsts.addAll(first.getNonTheoryConsts());
		nonTheoryConsts.addAll(second.getNonTheoryConsts());
		final Substitution sub = new Substitution(mMgScript, substitute);
		final Term transformedSecond = sub.transform(second.getFormula());
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, false,
				nonTheoryConsts, true, null, false);
		tfb.setFormula(mMgScript.getScript().term("and", first.getFormula(), transformedSecond));
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mMgScript);
	}
	
	@SuppressWarnings("unchecked")
	private List<INLOC> getLoopHeads(){
		//TODO how can I guaranty to pick the right LoopHead
		//Example: ambigousLoopEntry - L13loopEntry vs L14
		
		List<INLOC> loopHeads = new ArrayList<>();
		Set<INLOC> markedNodes = new HashSet<>();
		List<INLOC> openNodes = new ArrayList<>(mOriginalIcfg.getInitialNodes());

		while(!openNodes.isEmpty()){
			INLOC openNode = openNodes.remove(0);
			if(markedNodes.contains(openNode)){
				loopHeads.add(openNode);
			}else{
				openNode.getOutgoingEdges().forEach(edge -> {
					if(!openNodes.contains(edge.getTarget())) {
						openNodes.add((INLOC) edge.getTarget());
						}
					});
			}
			markedNodes.add(openNode);
		}
		return loopHeads;
	}

	public IIcfg<OUTLOC> rejoin(SimpleLoop originalLoop, Term result, Map<IProgramVar, Term> values,  TermVariable n) {
		final Script script = mMgScript.getScript();
		final UnmodifiableTransFormula originalLoopTransFormula = originalLoop.mLoopTransFormula;
		final Map<IcfgEdge, UnmodifiableTransFormula> loopExits = new HashMap<>();
		final IcfgLocation loopHead = originalLoop.mHeadNode;
		
		for(IcfgEdge exitEdge : originalLoop.mExitEdges){
			// get LoopExit
			UnmodifiableTransFormula exitTransformula = exitEdge.getTransformula();
	
			// joint the TransFormula
			final Map<Term, Term> substitute = new HashMap<>();
			final Map<IProgramVar, TermVariable> outVars = new HashMap<>(exitTransformula.getOutVars());
			for (final IProgramVar var : originalLoopTransFormula.getOutVars().keySet()) {
				if (exitTransformula.getInVars().containsKey(var)) {
					substitute.put(exitTransformula.getInVars().get(var), values.get(var));
					if (exitTransformula.getInVars().get(var).equals(exitTransformula.getOutVars().get(var))) {
						outVars.remove(var);
						outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
					}
				} else {
					outVars.put(var, originalLoopTransFormula.getOutVars().get(var));
				}
			}
	
			final Substitution sub = new Substitution(mMgScript, substitute);
			final Term transformedExitFormula = script.term("not", sub.transform(exitTransformula.getFormula()));
			Term jointTerm = script.term("and", transformedExitFormula, result);

			//Quantifier - Start
			
//			//replace n with j
//			TermVariable j = script.variable("j", script.sort("Int"));
//			final Map<Term, Term> substituteJ = new HashMap<>();
//			substituteJ.put(n, j);
//			final Substitution subJ = new Substitution(mMgScript, substituteJ);
//			final Term transformedExitFormulaJ = subJ.transform(transformedExitFormula);
//			
//			final Term zero = script.numeral("0");
//			final Term conditions = script.term("xor", script.term(">=", j, n), script.term("or", script.term("<", j, zero), transformedExitFormulaJ));
//			final Term quantifiedFormula = script.quantifier(Script.FORALL, new TermVariable[] {j}, conditions);
//			final Term simplified = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgScript,
//					quantifiedFormula, SimplificationTechnique.SIMPLIFY_DDA,
//					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
//			jointTerm = script.term("and", simplified, result);
			
			//Quantifier - End
			
			final TransFormulaBuilder tfb = new TransFormulaBuilder(originalLoopTransFormula.getInVars(), outVars, false,
					originalLoopTransFormula.getNonTheoryConsts(), true, null, false);			
			tfb.setFormula(jointTerm);
			tfb.addAuxVar(n);
			tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
			final UnmodifiableTransFormula loop = tfb.finishConstruction(mMgScript);
			loopExits.put(exitEdge, loop);
		}
		
		// create icfg
		mOriginalIcfg.getIdentifier();
		final BasicIcfg<OUTLOC> resultIcfg =
				new BasicIcfg<>(mNewIcfgIdentifier, mOriginalIcfg.getCfgSmtToolkit(), mOutLocationClass);
		final TransformedIcfgBuilder<INLOC, OUTLOC> lst = new TransformedIcfgBuilder<>(mFunLocFac,
				mBacktranslationTracker, mTransformer, mOriginalIcfg, resultIcfg);
		processLocations(mOriginalIcfg.getInitialNodes(), lst, loopHead, loopExits);
		lst.finish();
		return resultIcfg;
	}
	
	private void processLocations(final Set<INLOC> init, final TransformedIcfgBuilder<INLOC, OUTLOC> lst, 
			IcfgLocation loopHead, Map<IcfgEdge, UnmodifiableTransFormula> loopExits) {
		final Deque<INLOC> open = new ArrayDeque<>(init);
		final Set<INLOC> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final INLOC oldSource = open.removeFirst();
			if (!closed.add(oldSource)) {
				continue;
			}
			if (oldSource.equals(loopHead)) {
				final OUTLOC newSource = lst.createNewLocation(oldSource);
				
				for (final IcfgEdge oldTransition : loopExits.keySet()) {
					final INLOC oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);
					final IcfgInternalTransition newTransition = new IcfgInternalTransition(newSource, newTarget,
							getPayloadIfAvailable(oldTransition), loopExits.get(oldTransition));
					//TODO when is it an over-approximation
					new Overapprox("loop acceleration: ... ", null).annotate(newTransition);
					newSource.addOutgoing(newTransition);
					newTarget.addIncoming(newTransition);
					mBacktranslationTracker.rememberRelation(oldTransition, newTransition);
					mLogger.debug("Final-" + newTransition.getTransformula().getFormula().toStringDirect());
				}
			} else {
				final OUTLOC newSource = lst.createNewLocation(oldSource);
				for (final IcfgEdge oldTransition : oldSource.getOutgoingEdges()) {
					final INLOC oldTarget = (INLOC) oldTransition.getTarget();
					open.add(oldTarget);
					final OUTLOC newTarget = lst.createNewLocation(oldTarget);
					lst.createNewTransition(newSource, newTarget, oldTransition);
				}
			}
		}
	}

	private static IPayload getPayloadIfAvailable(final IElement elem) {
		if (elem == null) {
			return null;
		}
		if (elem.hasPayload()) {
			return elem.getPayload();
		}
		return null;
	}
}
