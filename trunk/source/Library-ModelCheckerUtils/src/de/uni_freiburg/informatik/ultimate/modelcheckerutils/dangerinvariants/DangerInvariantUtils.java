/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.dangerinvariants;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Class contains static auxiliary methods
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class DangerInvariantUtils {


	private DangerInvariantUtils() {
		// do not instanciate
	}

	/**
	 * Given a predicate predec and all its successors (as a HashRelation
	 * from IActions to IPredicates) succs. Check if every state that satisfies
	 * predec has some successor state.
	 *
	 * @param mgdScript
	 * @param services
	 * @param csToolkit
	 * @param predicateFactory
	 * @param logger
	 * @return
	 */
	public static Validity eachStateHasSuccessor(final IPredicate predec,
			final HashRelation<IAction, IPredicate> succs, final ManagedScript mgdScript, final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit, final BasicPredicateFactory predicateFactory, final ILogger logger) {
		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<Term, IPredicate, TransFormula>(
				mgdScript, new TermDomainOperationProvider(services, mgdScript));
		final Collection<IPredicate> predecessors = new ArrayList<IPredicate>();
		for (final Entry<IAction, IPredicate> entry : succs.entrySet()) {
			final Term pre = constructPreInternal(logger, predicateFactory, csToolkit, pt, entry.getKey().getTransformula(), entry.getValue(), services);
			predecessors.add(predicateFactory.newPredicate(pre));
		}
		final IPredicate disjunction = predicateFactory.or(true, predecessors);
		final MonolithicImplicationChecker mic = new MonolithicImplicationChecker(services, mgdScript);
		final Validity result = mic.checkImplication(predec, false, disjunction, false);
		return result;
	}

	/**
	 * Check if a given predicate is satisfied for at least one program state.
	 */
	public static Validity predicateIsNotEmpty(final IPredicate pred, final ManagedScript mgdScript) {
		final LBool lbool = SmtUtils.checkSatTerm(mgdScript.getScript(), pred.getClosedFormula());
		return IHoareTripleChecker.convertLBool2Validity(lbool);
	}


	private static Term constructPreInternal(final ILogger logger, final BasicPredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final PredicateTransformer<Term, IPredicate, TransFormula> pt,
			final TransFormula tf, final IPredicate succPred, final IUltimateServiceProvider services) {
		final Term wp = pt.weakestPrecondition(predicateFactory.not(succPred), tf);
		final Term wpLessQuantifiers = PartialQuantifierElimination.tryToEliminate(services, logger,
				csToolkit.getManagedScript(), wp, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final Term pre = SmtUtils.not(csToolkit.getManagedScript().getScript(), wpLessQuantifiers);
		return pre;
	}

	/**
	 * Checks whether a given danger invariant is correct.
	 *
	 * @param invariants
	 *            the danger invariant for each location
	 * @param icfg
	 * @param mgdScript
	 * @param services
	 * @param predicateFactory
	 * @param logger
	 * @return VALID if the danger invariant is correct
	 */
	public static Validity checkDangerInvariant(final Map<IcfgLocation, IPredicate> invariants, final IIcfg<?> icfg,
			final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final BasicPredicateFactory predicateFactory, final ILogger logger) {
		for (final IcfgLocation location : icfg.getInitialNodes()) {
			// TODO: This returns INVALID when it is correct ???
			final Validity validity = predicateIsNotEmpty(invariants.get(location), mgdScript);
			if (validity == Validity.VALID) {
				return Validity.INVALID;
			} else if (validity != Validity.INVALID) {
				return validity;
			}
		}

		final Deque<IcfgLocation> open = new ArrayDeque<>(icfg.getInitialNodes());
		final Set<IcfgLocation> closed = new HashSet<>();

		while (!open.isEmpty()) {
			final IcfgLocation location = open.pop();
			closed.add(location);

			if (IcfgUtils.isErrorLocation(icfg, location)) {
				continue;
			}

			final HashRelation<IAction, IPredicate> relation = new HashRelation<>();
			for (final IcfgEdge transition : location.getOutgoingEdges()) {
				final IcfgLocation target = transition.getTarget();
				relation.addPair(transition, invariants.get(target));
				if (!closed.contains(target)) {
					open.add(target);
				}
			}

			final Validity validity = eachStateHasSuccessor(invariants.get(location), relation, mgdScript, services,
					icfg.getCfgSmtToolkit(), predicateFactory, logger);
			if (validity != Validity.VALID) {
				return validity;
			}
		}

		return Validity.VALID;
	}
}
