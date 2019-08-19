/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayDeque;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Compute underapproximations (resp. overapproximations) of invariants
 * using sp (resp. wp).
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class NonInductiveAnnotationGenerator {
	
	public enum Approximation {
		OVERAPPROXIMATION,
		UNDERAPPROXIMATION,
	}

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IIcfg<?> mIcfg;
	
	private final HashRelation<IcfgLocation, IPredicate> mResult = new HashRelation<>();
	private final ArrayDeque<Pair<IcfgLocation, IPredicate>> mWorklist = new ArrayDeque<>();
	private final Predicate<Pair<IcfgLocation, IcfgLocation>> mExitCondition;
	
	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA; 
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
	
	private final Approximation mApproximation;
	
	


	public NonInductiveAnnotationGenerator(final IUltimateServiceProvider services, final BasicPredicateFactory basicPredicateFactory,
			final IIcfg<?> icfg, final Approximation approximation) {
		super();
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPredicateFactory = basicPredicateFactory;
		mIcfg = icfg;
		mManagedScript = icfg.getCfgSmtToolkit().getManagedScript();
		mPredicateTransformer = new PredicateTransformer<Term, IPredicate, TransFormula>(mManagedScript, new TermDomainOperationProvider(mServices, mManagedScript));
		mApproximation = approximation;
		mExitCondition = constructExitCondition_OnlyOne();
		switch (mApproximation) {
		case OVERAPPROXIMATION:
			initializeWorklistForOverapproximation();
			break;
		case UNDERAPPROXIMATION:
			initializeWorklistForUnderapproximation();
			break;
		default:
			break;
		}
		
		while (!mWorklist.isEmpty()) {
			final Pair<IcfgLocation, IPredicate> annot = mWorklist.removeFirst();
			switch (mApproximation) {
			case OVERAPPROXIMATION:
				processAnnotationForOverapproximation(annot.getFirst(), annot.getSecond(), mExitCondition);
				break;
			case UNDERAPPROXIMATION:
				processAnnotationForUnderapproximation(annot.getFirst(), annot.getSecond(), mExitCondition);
				break;
			default:
				break;
			}
			
		}
	}

	private void initializeWorklistForUnderapproximation() {
		for (final IcfgLocation init : mIcfg.getInitialNodes()) {
			final Term term = mManagedScript.getScript().term("true");
			addNewTerm(init, term);
		}
	}
	
	private void initializeWorklistForOverapproximation() {
		for (final IcfgLocation init : IcfgUtils.getErrorLocations(mIcfg)) {
			final Term term = mManagedScript.getScript().term("false");
			addNewTerm(init, term);
		}
	}
	
	/**
	 * Construct {@link Predicate} that can be used to stop iteration such
	 * that we obtain only one annotation per location. 
	 */
	private Predicate<Pair<IcfgLocation, IcfgLocation>> constructExitCondition_OnlyOne() {
		return new Predicate<Pair<IcfgLocation,IcfgLocation>>() {

			@Override
			public boolean test(final Pair<IcfgLocation, IcfgLocation> predSucc) {
				return mResult.getDomain().contains(predSucc.getSecond());
			}
		};
	}
	
	private void addNewTerm(final IcfgLocation loc, final Term term) {
		final IPredicate p = mPredicateFactory.newPredicate(term);
		mResult.addPair(loc, p);
		mWorklist.add(new Pair<>(loc, p));
	}
	
	
	private void processAnnotationForUnderapproximation(final IcfgLocation loc, final IPredicate p, 
			final Predicate<Pair<IcfgLocation,IcfgLocation>> exitCondition) {
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			final IcfgLocation succ = edge.getTarget();
			if (exitCondition.test(new Pair<>(loc, succ))) {
				// do not continue here
			} else {
				if (edge.getLabel() instanceof IInternalAction) {
					final IInternalAction action = (IInternalAction) edge.getLabel();
					final Term succTerm = mPredicateTransformer.strongestPostcondition(p, action.getTransformula());
					final Term lessQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, 
							mManagedScript, succTerm, mSimplificationTechnique, 
							mXnfConversionTechnique);
					addNewTerm(edge.getTarget(), lessQuantifiers);
				} else {
					throw new UnsupportedOperationException("interprocedural programs not yet supported");
				}
			}
		}
	}
	
	private void processAnnotationForOverapproximation(final IcfgLocation loc, final IPredicate p, 
			final Predicate<Pair<IcfgLocation,IcfgLocation>> exitCondition) {
		for (final IcfgEdge edge : loc.getIncomingEdges()) {
			final IcfgLocation pred = edge.getSource();
			if (exitCondition.test(new Pair<>(loc, pred))) {
				// do not continue here
			} else {
				if (edge.getLabel() instanceof IInternalAction) {
					final IInternalAction action = (IInternalAction) edge.getLabel();
					final Term succTerm = mPredicateTransformer.weakestPrecondition(p, action.getTransformula());
					final Term lessQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, 
							mManagedScript, succTerm, mSimplificationTechnique, 
							mXnfConversionTechnique);
					addNewTerm(edge.getSource(), lessQuantifiers);
				} else {
					throw new UnsupportedOperationException("interprocedural programs not yet supported");
				}
			}
		}
	}
	
	
	
	public HashRelation<IcfgLocation, IPredicate> getResult() {
		return mResult;
	}

	

	
}
