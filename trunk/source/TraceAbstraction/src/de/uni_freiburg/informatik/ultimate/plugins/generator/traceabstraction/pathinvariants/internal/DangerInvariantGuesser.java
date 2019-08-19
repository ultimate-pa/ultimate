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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.dangerinvariants.DangerInvariantUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DagSizePrinter;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.LargeBlockEncodingIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

/**
 * Computes a "danger invariant candidate" by abstracting every transition by its "guarded havoc"
 * {@link TransFormulaUtils#computeGuardedHavoc} and iterating backwards over the CFG starting from the error locations.
 * <p>
 * We call a mapping from locations to predicates a "danger invariant candidate" if the following is satisfied.
 * <ul>
 * <li>every error location is mapped to "true"
 * <li>every state that satisfies the invariant and whose location is not an error location has at least one successor
 * that satisfies the invariant
 * </ul>
 * (TODO Matthias 2018-12-22: Hence a "danger invariant candidate" is a (partial) danger invariant where we do not
 * require that the initial location is mapped to a satisfiable predicate. I "invented" this term, I do not like it,
 * maybe we should contact the Danger Invariant authors and ask for a better suggestion.)
 * <p>
 * For the computation, we (conceptually) first annotate all non-error locations with "false" and all error locations
 * with true. The we iterate backwards over the CFG by adding all error locations to the worklist. Let ϕ be the mapping
 * from locations to predicates. Let gh(act) be the guarded havoc of the action act. For every edge (loc,act,loc') where
 * loc' is in the worklist we compute pre(ϕ(loc'), gh(act)) and set ϕ(loc) to the following disjunction.
 * <p>
 * ϕ(loc) \/ re(ϕ(loc'), gh(act))
 * <p>
 * If the annotation of the location loc was changed by this update we add loc to the worklist. Since the guarded havoc
 * is a very coarse abstraction every location is visited only a finite number of times and this process terminates. If
 * the initial location is annotated by a satisfiable predicate, the danger invariant candidate is a danger invariant.
 * <p>
 * Possible improvements: A. improve the computation of {@link TransFormulaUtils#computeGuardedHavoc} as proposed in the
 * documentation there. B. Detect in advance which edges occur in a loop Use the guarded havoc only in loops and the
 * original transformula outside of loops.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class DangerInvariantGuesser {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Map<IcfgLocation, IPredicate> mCandidateInvariant;

	private final IIcfg<IcfgLocation> mIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;

	public DangerInvariantGuesser(final IIcfg<IcfgLocation> inputIcfg, final IUltimateServiceProvider services,
			final IPredicate precondition, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;

		mIcfg = applyLargeBlockEncoding(inputIcfg, predicateFactory, predicateUnifier);

		try {
			mCandidateInvariant =
					computeCandidateInvariant(services, predicateFactory, predicateUnifier, csToolkit, mIcfg);
		} catch (final ToolchainCanceledException tce) {
			final String taskDescription = "traversing ICFG of " + IcfgUtils.getNumberOfLocations(mIcfg) + " locations";
			tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
			throw tce;
		}

	}

	public Map<IcfgLocation, IPredicate> getCandidateInvariant() {
		return mCandidateInvariant;
	}

	public boolean isDangerInvariant() {
		final Validity isDangerInvariant = DangerInvariantUtils.checkDangerInvariant(mCandidateInvariant, mIcfg,
				mCsToolkit.getManagedScript(), mServices, mPredicateFactory, mLogger);
		return (isDangerInvariant == Validity.VALID);
	}

	private IIcfg<IcfgLocation> applyLargeBlockEncoding(final IIcfg<IcfgLocation> pathProgram,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier) {
		IIcfg<IcfgLocation> icfg;
		final LargeBlockEncodingIcfgTransformer lbeTransformer =
				new LargeBlockEncodingIcfgTransformer(mServices, predicateFactory, predicateUnifier);
		icfg = lbeTransformer.transform(pathProgram);
		return icfg;
	}

	private Map<IcfgLocation, IPredicate> computeCandidateInvariant(final IUltimateServiceProvider services,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit, final IIcfg<IcfgLocation> icfg) {
		final Set<IcfgLocation> errorLocations = IcfgUtils.getErrorLocations(icfg);
		final LinkedHashSet<IcfgLocation> worklist = new LinkedHashSet<>();
		final Map<IcfgLocation, IPredicate> candidateInvariant = new HashMap<>();
		for (final IcfgLocation errorLoc : errorLocations) {
			final IPredicate truePredicate = predicateUnifier.getTruePredicate();
			candidateInvariant.put(errorLoc, truePredicate);
			worklist.add(errorLoc);
		}

		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));
		while (!worklist.isEmpty()) {

			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(this.getClass(),
						"processing worklist containing " + worklist.size() + " elements");
			}

			final Iterator<IcfgLocation> it = worklist.iterator();
			final IcfgLocation cur = it.next();
			it.remove();
			for (final IcfgEdge edge : cur.getIncomingEdges()) {
				final IPredicate p = candidateInvariant.get(cur);
				final UnmodifiableTransFormula tf = edge.getTransformula();
				UnmodifiableTransFormula tfnew = null;
				try {
					tfnew = TransFormulaUtils.computeGuardedHavoc(tf, csToolkit.getManagedScript(), services, mLogger,
							true);
				} catch (final ToolchainCanceledException tce) {
					final String taskDescription = "computing guarded havoc for TransFormula of DAG size "
							+ new DagSizePrinter(tf.getFormula());
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				}
				final Term preTerm;
				try {
					preTerm = computePre(pt, p, tfnew, predicateFactory, csToolkit);
				} catch (final ToolchainCanceledException tce) {
					final String taskDescription =
							"computing PRE for IPredicate of DAG size " + new DagSizePrinter(p.getFormula())
									+ " and TransFormula of DAG size " + new DagSizePrinter(tf.getFormula());
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				}
				final IcfgLocation sourceLoc = edge.getSource();
				final IPredicate sourcePred = candidateInvariant.get(sourceLoc);
				if (sourcePred == null) {
					final IPredicate pre = predicateUnifier.getOrConstructPredicate(preTerm);
					candidateInvariant.put(sourceLoc, pre);
					worklist.add(sourceLoc);
				} else {
					final IPredicate newSourcePred = predicateUnifier.getOrConstructPredicate(
							SmtUtils.or(csToolkit.getManagedScript().getScript(), sourcePred.getFormula(), preTerm));
					if (newSourcePred == sourcePred) {
						// no nothing
					} else {
						candidateInvariant.put(sourceLoc, newSourcePred);
						worklist.add(sourceLoc);
					}
				}
			}
		}
		addFalseToRemainingLocations(icfg, candidateInvariant, predicateUnifier.getFalsePredicate());
		return candidateInvariant;
	}

	private void addFalseToRemainingLocations(final IIcfg<IcfgLocation> icfg,
			final Map<IcfgLocation, IPredicate> candidateInvariant, final IPredicate falsePredicate) {
		for (final Entry<String, Map<DebugIdentifier, IcfgLocation>> entry1 : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, IcfgLocation> entry2 : entry1.getValue().entrySet()) {
				final IcfgLocation loc = entry2.getValue();
				if (!candidateInvariant.containsKey(loc)) {
					candidateInvariant.put(loc, falsePredicate);
				}
			}
		}
	}

	private Term computePre(final PredicateTransformer<Term, IPredicate, TransFormula> pt, final IPredicate p,
			final UnmodifiableTransFormula tf, final BasicPredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit) {
		final Term wp = pt.weakestPrecondition(predicateFactory.not(p), tf);
		final Term wpLessQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
				csToolkit.getManagedScript(), wp, SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		final Term pre = SmtUtils.not(csToolkit.getManagedScript().getScript(), wpLessQuantifiers);
		return pre;
	}

}
