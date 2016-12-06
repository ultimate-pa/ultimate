/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayEquality.ArrayEqualityExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPPostOperator implements IAbstractPostOperator<VPState, CodeBlock, IProgramVar> {
	
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;

	private final VPDomain mDomain;

	public VPPostOperator(final ManagedScript script, final IUltimateServiceProvider services, final VPDomain domain) {
		mScript = script;
		mServices = services;
		mDomain = domain;
	}
	
	@Override
	public List<VPState> apply(final VPState oldstate, final CodeBlock transition) {
		
		final UnmodifiableTransFormula tf = transition.getTransitionFormula();
		if (tf.getOutVars().isEmpty()) {
			return Collections.singletonList(oldstate);
		}

		if (oldstate instanceof VPStateBottom) {
			return Collections.singletonList(mDomain.getVpStateFactory().getBottomState());
		}

		final Term nnfTerm = new Nnf(mScript, mServices, QuantifierHandling.CRASH).transform(tf.getFormula());

		mDomain.getLogger().debug("Original term: " + tf.getFormula());
		mDomain.getLogger().debug("Nnf term:      " + nnfTerm);
		
		final Term term = nnfTerm;

		final VPState preparedState = mDomain.getVpStateFactory().havocVariables(tf.getAssignedVars(), oldstate);

		final Map<TermVariable, IProgramVar> tvToPvMap = VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf);

		final List<VPState> resultStates = handleTransition(preparedState, term, tvToPvMap, false);

		mDomain.getLogger().debug("states after transition " + transition + ": " + resultStates);

		return resultStates;
	}

	private List<VPState> handleTransition(final VPState preState, final Term term,
			final Map<TermVariable, IProgramVar> tvToPvMap, final boolean negated) {
		
		if (term instanceof ApplicationTerm) {
			
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String applicationName = appTerm.getFunction().getName();

			if (applicationName == "and") {
				assert !negated : "we transformed to nnf before, right?";

				final List<List<VPState>> andList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					andList.add(handleTransition(preState, t, tvToPvMap, false));
				}

				assert andList.size() > 1;

				final List<VPState> result = new ArrayList<>();
				final List<VPState> state = new ArrayList<>();
				state.addAll(andList.get(0));
				for (int i = 1; i < andList.size(); i++) {
					for (int j = 0; j < state.size(); j++) {
						for (int k = 0; k < andList.get(i).size(); k++) {
							result.addAll(mDomain.getVpStateFactory().conjoin(state.get(j), andList.get(i).get(k)));
						}
					}
					state.clear();
					state.addAll(result);
					if (!(i == andList.size() - 1)) {
						result.clear();
					}
				}
				return result;
			} else if (applicationName == "or") {
				assert !negated : "we transformed to nnf before, right?";

				final List<VPState> orList = new ArrayList<>();
				for (final Term t : appTerm.getParameters()) {
					orList.addAll(handleTransition(preState, t, tvToPvMap, false));
				}
				return orList;
			} else if (applicationName == "=") {
				/*
				 * case "ArrayEquality"
				 */
				final List<ArrayEquality> aeqs =
						new ArrayEqualityExtractor(new Term[] { appTerm }).getArrayEqualities();
				if (!aeqs.isEmpty()) {
					assert aeqs.size() == 1 : "?";
					// we have an array equality (i.e. something like (= a b) where a,b are arrays)
					return new ArrayList<>(handleArrayEqualityTransition(preState, tvToPvMap, negated, aeqs.get(0)));
				}

				/*
				 * case "ArrayUpdate"
				 */
				final List<ArrayUpdate> aus = new ArrayUpdateExtractor(false, false, appTerm).getArrayUpdates();
				
				if (!aus.isEmpty()) {
					assert aus.size() == 1 : "?";
					// we have an array update
					return new ArrayList<>(handleArrayUpdateTransition(preState, tvToPvMap, negated, aus.get(0)));
				}

				/*
				 * case "two terms we track are equated"
				 */
				final EqNode node1 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[0], tvToPvMap);
				final EqNode node2 = mDomain.getPreAnalysis().getEqNode(appTerm.getParameters()[1], tvToPvMap);
				
				if (node1 != null && node2 != null) {
					if (!negated) {
						final Set<VPState> resultStates =
								mDomain.getVpStateFactory().addEquality(node1, node2, preState);
						return new ArrayList<>(resultStates);
					} else {
						final Set<VPState> resultStates =
								mDomain.getVpStateFactory().addDisEquality(node1, node2, preState);
						return new ArrayList<>(resultStates);
					}
				}

				/*
				 * case "otherwise" --> we leave the state unchanged
				 */
				return Collections.singletonList(preState);
			} else if (applicationName == "not") {
				assert !negated : "we transformed to nnf before, right?";
				return handleTransition(preState, appTerm.getParameters()[0], tvToPvMap, !negated);
			} else if (applicationName == "distinct") {
				
				final Term equality =
						mScript.getScript().term("=", appTerm.getParameters()[0], appTerm.getParameters()[1]);

				return handleTransition(preState, equality, tvToPvMap, !negated);
			}
			
		} else if (term instanceof QuantifiedFormula) {
			// return handleTransition(preState, ((QuantifiedFormula) term).getSubformula(), tvToPvMap);
			assert false : "we currently cannot deal with quantifiers";
			return null;
		} else if (term instanceof AnnotatedTerm) {
			return handleTransition(preState, ((AnnotatedTerm) term).getSubterm(), tvToPvMap, negated);
		}
		/*
		 * no part of the TransFormula influences the state --> return a copy
		 */

		VPState resultState = preState;//mDomain.getVpStateFactory().copy(preState).build();
		return Collections.singletonList(resultState);
	}
	
	private Set<VPState> handleArrayEqualityTransition(final VPState preState,
			final Map<TermVariable, IProgramVar> tvToPvMap, final boolean negated, final ArrayEquality aeq) {
		final Term array1Term = aeq.getLhs();
		final Term array2Term = aeq.getRhs();
		final IProgramVarOrConst array1 =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array1Term, tvToPvMap);
		final IProgramVarOrConst array2 =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(array2Term, tvToPvMap);
		if (!negated) {
			final Set<VPState> resultStates = mDomain.getVpStateFactory().arrayEquality(array1, array2, preState);
			return resultStates;
		} else {
			/*
			 * something of the form a != b where a and b are arrays
			 *  --> we cannot derive anything from this because we only track a finite number
			 *     of positions in each (infinite) array
			 */
			return Collections.singleton(preState);
		}
	}
	
	private Set<VPState> handleArrayUpdateTransition(final VPState preState,
			final Map<TermVariable, IProgramVar> tvToPvMap, final boolean negated, final ArrayUpdate au) {
		final MultiDimensionalStore mdStore = au.getMultiDimensionalStore();
		final TermVariable newArrayTv = au.getNewArray();
		final Term oldArrayTerm = au.getOldArray();
		final Term value = au.getValue();

		final IProgramVarOrConst newArrayId =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(newArrayTv, tvToPvMap);
		final IProgramVarOrConst oldArrayId =
				mDomain.getPreAnalysis().getIProgramVarOrConstOrLiteral(oldArrayTerm, tvToPvMap);

		if (newArrayId.equals(oldArrayId)) {
			assert newArrayId == oldArrayId : "right?..";
			/*
			 * we essentially have something of the form a[i_1, ..,i_n] := v; in terms of Boogie --> we only havoc the
			 * EqNode belonging to a[i_1, ..,i_n] and add an equality to v
			 */

			// TODO: strictly speaking we have to check here, that newArrayId is an outVar, oldArrayId an inVar

			final EqNode arrayAtIndexNode = mDomain.getPreAnalysis().getEqNode(mdStore.getStoreTerm(), tvToPvMap);
			final EqNode valueNode = mDomain.getPreAnalysis().getEqNode(value, tvToPvMap);

			if (!negated) {
				final VPState resultState = mDomain.getVpStateFactory().havoc(arrayAtIndexNode, preState);
				final Set<VPState> resultStates = new HashSet<>();
				resultStates.addAll(mDomain.getVpStateFactory().addEquality(arrayAtIndexNode, valueNode, resultState));
				return resultStates;
			} else {
				assert false : "TODO";// TODO
				return null;
			}
		} else {
			/*
			 * we have something of the form b := a[(i_1, ..,i_n) := v] in terms of Boogie -->
			 */
		
			if (!negated) {
//				TODO: treat essentially like an ArrayEquality (except for that one point)
				assert false : "does this occur?";
			
			/*
			 * for all points p except (i_1, .., i_n), we add 
			 *   b[p] = a[p] to the state
			 * and we add b[i_1, ..., i_n] = v
			 */
			
				return null;
			} else {
				/*
				 * see the "negated" case in handleArrayEquality for an explanation
				 */
				return Collections.singleton(preState);
			}
		}
	}
	
	@Override
	public List<VPState> apply(final VPState stateBeforeLeaving, final VPState stateAfterLeaving,
			final CodeBlock transition) {
		// List<VPState> conjoined = mDomain.getVpStateFactory().conjoin(stateBeforeLeaving, stateAfterLeaving);

		// TODO
		
		// return apply(conjoined, transition);
		return null;
	}
	
}
