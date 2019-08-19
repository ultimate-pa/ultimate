/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Hoare annotation for invariants computed by single CEGAR loop
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationComposer {

	private static final boolean AVOID_IMPLICATIONS = true;
	/**
	 * What is the precondition for a context? Strongest postcondition or entry given by automaton?
	 */
	private static final boolean USE_ENTRY = true;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final HoareAnnotationFragments<?> mHoareAnnotationFragments;

	private final HoareAnnotationStatisticsGenerator mHoareAnnotationStatisticsGenerator;

	private final NestedMap2<IcfgLocation, IPredicate, Term> mLoc2callPred2disjunction;

	private int mNumberOfFragments = 0;
	private final Map<IcfgLocation, IPredicate> mLoc2hoare;

	private final IPredicate mSurrogateForEmptyCallPred;

	public HoareAnnotationComposer(final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final HoareAnnotationFragments<?> hoareAnnotationFragments, final IUltimateServiceProvider services,
			final SimplificationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mHoareAnnotationFragments = hoareAnnotationFragments;
		mHoareAnnotationStatisticsGenerator = new HoareAnnotationStatisticsGenerator();
		mSurrogateForEmptyCallPred =
				mPredicateFactory.newPredicate(mCsToolkit.getManagedScript().getScript().term("true"));
		final HashRelation3<IcfgLocation, IPredicate, Term> loc2callPred2disjuncts =
				constructLoc2CallPred2DisjunctsMapping();
		mLoc2callPred2disjunction = constructLoc2Callpred2DisjunctionMapping(loc2callPred2disjuncts);
		mHoareAnnotationStatisticsGenerator.setNumberOfFragments(mNumberOfFragments);
		mHoareAnnotationStatisticsGenerator.setLocationsWithHoareAnnotation(mLoc2callPred2disjunction.keySet().size());
		mHoareAnnotationStatisticsGenerator.setPreInvPairs(mLoc2callPred2disjunction.size());
		mLoc2hoare = combineInter(mLoc2callPred2disjunction);

	}

	private Map<IcfgLocation, IPredicate>
			combineInter(final NestedMap2<IcfgLocation, IPredicate, Term> loc2callPred2invariant) {
		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		for (final IcfgLocation loc : loc2callPred2invariant.keySet()) {
			final Map<IPredicate, Term> callpred2invariant = loc2callPred2invariant.get(loc);
			final List<Term> conjuncts = new ArrayList<>(callpred2invariant.size());
			for (final Entry<IPredicate, Term> entry : callpred2invariant.entrySet()) {

				final IPredicate postForCallpred;
				if (USE_ENTRY || containsAnOldVar(entry.getKey())) {
					if (entry.getKey() == mSurrogateForEmptyCallPred) {
						postForCallpred = mSurrogateForEmptyCallPred;
					} else {
						postForCallpred = mHoareAnnotationFragments.getCallpred2Entry().get(entry.getKey());
					}
					assert postForCallpred != null : "no post for callpred";
				} else {
					// compute SP
					throw new AssertionError("not implemented");
				}
				final Term precond = TraceAbstractionUtils.renameGlobalsToOldGlobals(postForCallpred, mServices,
						mCsToolkit.getManagedScript());

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("In " + loc + " holds " + entry.getValue() + " for precond " + precond);
				}
				Term precondImpliesInvariant =
						Util.implies(mCsToolkit.getManagedScript().getScript(), precond, entry.getValue());
				if (AVOID_IMPLICATIONS) {
					precondImpliesInvariant = new NnfTransformer(mCsToolkit.getManagedScript(), mServices, QuantifierHandling.KEEP)
							.transform(precondImpliesInvariant);
				}
				conjuncts.add(precondImpliesInvariant);
			}
			Term conjunction = SmtUtils.and(mCsToolkit.getManagedScript().getScript(), conjuncts);

			final Set<IProgramVar> vars = TermVarsProc.computeTermVarsProc(conjunction,
					mCsToolkit.getManagedScript().getScript(), mCsToolkit.getSymbolTable()).getVars();
			conjunction = TraceAbstractionUtils.substituteOldVarsOfNonModifiableGlobals(loc.getProcedure(), vars,
					conjunction, mCsToolkit.getModifiableGlobalsTable(), mCsToolkit.getManagedScript().getScript());
			final ExtendedSimplificationResult simplificationResult = SmtUtils.simplifyWithStatistics(
					mCsToolkit.getManagedScript(), conjunction, null, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			mHoareAnnotationStatisticsGenerator.reportSimplificationInter();
			mHoareAnnotationStatisticsGenerator.reportReductionInter(simplificationResult.getReductionOfTreeSize());
			mHoareAnnotationStatisticsGenerator
					.reportSimplificationTimeInter(simplificationResult.getSimplificationTimeNano());
			mHoareAnnotationStatisticsGenerator
					.reportAnnotationSize(new DAGSize().treesize(simplificationResult.getSimplifiedTerm()));
			final Term simplified = simplificationResult.getSimplifiedTerm();
			final Term pnf =
					SmtUtils.constructPositiveNormalForm(mCsToolkit.getManagedScript().getScript(), simplified);
			final BasicPredicate pred = mPredicateFactory.newPredicate(pnf);
			result.put(loc, pred);
		}
		return result;
	}

	private NestedMap2<IcfgLocation, IPredicate, Term> constructLoc2Callpred2DisjunctionMapping(
			final HashRelation3<IcfgLocation, IPredicate, Term> loc2precond2invariantSet) {
		final NestedMap2<IcfgLocation, IPredicate, Term> loc2precond2invariant = new NestedMap2<>();
		for (final IcfgLocation loc : loc2precond2invariantSet.projectToFst()) {
			for (final IPredicate precond : loc2precond2invariantSet.projectToSnd(loc)) {
				final Set<Term> terms = loc2precond2invariantSet.projectToTrd(loc, precond);
				mNumberOfFragments += terms.size();
				final Term invariant = or(terms);
				loc2precond2invariant.put(loc, precond, invariant);
			}
		}
		return loc2precond2invariant;
	}

	private Term or(final Set<Term> terms) {
		final Term disjunction = SmtUtils.or(mCsToolkit.getManagedScript().getScript(), terms);
		final ExtendedSimplificationResult simplificationResult = SmtUtils.simplifyWithStatistics(
				mCsToolkit.getManagedScript(), disjunction, null, mServices, SimplificationTechnique.SIMPLIFY_QUICK);
		mHoareAnnotationStatisticsGenerator.reportSimplification();
		mHoareAnnotationStatisticsGenerator.reportReduction(simplificationResult.getReductionOfTreeSize());
		mHoareAnnotationStatisticsGenerator.reportSimplificationTime(simplificationResult.getSimplificationTimeNano());
		return simplificationResult.getSimplifiedTerm();
	}

	/**
	 * Construct mapping for our three cases: - invariants for empty callpred - invariants for dead callpred -
	 * invariants for live callpred
	 * 
	 */
	public HashRelation3<IcfgLocation, IPredicate, Term> constructLoc2CallPred2DisjunctsMapping() {
		final HashRelation3<IcfgLocation, IPredicate, Term> loc2callpred2invariant = new HashRelation3<>();

		addHoareAnnotationForCallPred(loc2callpred2invariant, mSurrogateForEmptyCallPred,
				mHoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (final IPredicate callPred : mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			final HashRelation<IcfgLocation, IPredicate> pp2preds =
					mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().get(callPred);
			addHoareAnnotationForCallPred(loc2callpred2invariant, callPred, pp2preds);
		}

		for (final IPredicate callPred : mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			final HashRelation<IcfgLocation, IPredicate> pp2preds =
					mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().get(callPred);
			addHoareAnnotationForCallPred(loc2callpred2invariant, callPred, pp2preds);
		}
		return loc2callpred2invariant;
	}

	/**
	 * Construct mapping for our three cases: - invariants for empty callpred - invariants for dead callpred -
	 * invariants for live callpred
	 * 
	 */
	public HashRelation3<IcfgLocation, IPredicate, Term> constructMappingOld() {
		final HashRelation3<IcfgLocation, IPredicate, Term> loc2callpred2invariant = new HashRelation3<>();

		final IPredicate surrogateForEmptyCallPred =
				mPredicateFactory.newPredicate(mCsToolkit.getManagedScript().getScript().term("true"));
		addHoareAnnotationForCallPred(loc2callpred2invariant, surrogateForEmptyCallPred,
				mHoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (final IPredicate context : mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			IPredicate precondForContext;
			if (USE_ENTRY || containsAnOldVar(context)) {
				precondForContext = mHoareAnnotationFragments.getCallpred2Entry().get(context);
			} else {
				// compute SP
				throw new AssertionError("not implemented");
			}
			precondForContext = TraceAbstractionUtils.renameGlobalsToOldGlobals(precondForContext, mServices,
					mCsToolkit.getManagedScript(), mPredicateFactory, SimplificationTechnique.SIMPLIFY_DDA);
			final HashRelation<IcfgLocation, IPredicate> pp2preds =
					mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForCallPred(loc2callpred2invariant, precondForContext, pp2preds);
		}

		for (final IPredicate context : mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			IPredicate precondForContext;
			if (USE_ENTRY || containsAnOldVar(context)) {
				precondForContext = mHoareAnnotationFragments.getCallpred2Entry().get(context);
			} else {
				// compute SP
				throw new AssertionError("not implemented");
			}
			precondForContext = TraceAbstractionUtils.renameGlobalsToOldGlobals(precondForContext, mServices,
					mCsToolkit.getManagedScript(), mPredicateFactory, SimplificationTechnique.SIMPLIFY_DDA);
			final HashRelation<IcfgLocation, IPredicate> pp2preds =
					mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForCallPred(loc2callpred2invariant, precondForContext, pp2preds);
		}
		return loc2callpred2invariant;
	}

	/**
	 * @param loc2callPred2invariant
	 * @param precondForContext
	 * @param pp2preds
	 */
	private static <DOM extends IcfgLocation> void addHoareAnnotationForCallPred(
			final HashRelation3<IcfgLocation, IPredicate, Term> loc2callPred2invariant,
			final IPredicate precondForContext, final HashRelation<DOM, IPredicate> pp2preds) {
		for (final DOM loc : pp2preds.getDomain()) {
			final Set<IPredicate> preds = pp2preds.getImage(loc);
			for (final IPredicate pred : preds) {
				loc2callPred2invariant.addTriple(loc, precondForContext, pred.getFormula());
			}
		}
	}

	private static boolean containsAnOldVar(final IPredicate p) {
		return p.getVars().stream().anyMatch(IProgramVar::isOldvar);
	}

	public HoareAnnotationStatisticsGenerator getHoareAnnotationStatisticsGenerator() {
		return mHoareAnnotationStatisticsGenerator;
	}

	public Map<IcfgLocation, IPredicate> getLoc2hoare() {
		return mLoc2hoare;
	}

}
