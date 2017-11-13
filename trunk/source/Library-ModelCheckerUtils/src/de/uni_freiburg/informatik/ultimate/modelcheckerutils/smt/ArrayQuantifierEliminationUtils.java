/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Provides auxiliary methods for our partitial quantifier elimination for arrays.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ArrayQuantifierEliminationUtils {

	public static EliminationTask elimAllSos(final EliminationTask eTask, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final ILogger logger) {
		final Set<ApplicationTerm> allSelectTerms = new ApplicationTermFinder("select", false).findMatchingSubterms(eTask.getTerm());
		final Map<Term, Term> substitutionMappingPre = new HashMap<>();
		final int singleCaseReplacements = 0;
		int multiCaseReplacements = 0;
		for (final ApplicationTerm selectTerm : allSelectTerms) {
			final MultiDimensionalSelectOverStore mdsos = MultiDimensionalSelectOverStore.convert(selectTerm);
			if (mdsos != null) {
				if (eTask.getEliminatees().contains(mdsos.getStore().getArray())) {
					final ArrayIndex selectIndex = mdsos.getSelect().getIndex();
					final ArrayIndex storeIndex = mdsos.getStore().getIndex();
//					final ThreeValuedEquivalenceRelation<Term> tver = analyzeIndexEqualities(selectIndex, storeIndex, quantifier, xjunctsOuter);
//					final EqualityStatus indexEquality = checkIndexEquality(selectIndex, storeIndex, tver);
//					switch (indexEquality) {
//					case EQUAL:
//						substitutionMappingPre.put(selectTerm, mdsos.constructEqualsReplacement());
//						singleCaseReplacements++;
//						break;
//					case NOT_EQUAL:
//						substitutionMappingPre.put(selectTerm, mdsos.constructNotEqualsReplacement(mScript));
//						singleCaseReplacements++;
//						break;
//					case UNKNOWN:
						substitutionMappingPre.put(selectTerm, transformMultiDimensionalSelectOverStoreToIte(mdsos, mgdScript));
						multiCaseReplacements++;
//						// do nothing
//						break;
//					default:
//						throw new AssertionError();
//					}
				}
			}
		}
		if (multiCaseReplacements > 0 || singleCaseReplacements > 0) {
			final Term replaced = new SubstitutionWithLocalSimplification(mgdScript, substitutionMappingPre).transform(eTask.getTerm());
//			if (multiCaseReplacements > 0) {
//				newAuxVars.add(eliminatee);
				final Term newTerm = new IteRemover(mgdScript).transform(replaced);
				final Term normal = new CommuhashNormalForm(services, mgdScript.getScript()).transform(newTerm);
				final Term simplified = SmtUtils.simplify(mgdScript, normal, services, SimplificationTechnique.SIMPLIFY_DDA);
				return new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), simplified);
//			}
		} else {
			return eTask;
		}
	}
	
	
	public static Term transformMultiDimensionalSelectOverStoreToIte(final MultiDimensionalSelectOverStore mdsos, final ManagedScript mgdScript) {
		final ArrayIndex selectIndex = mdsos.getSelect().getIndex();
		final ArrayIndex storeIndex = mdsos.getStore().getIndex();
		final Term eq = ArrayIndex.constructPairwiseEquality(selectIndex, storeIndex, mgdScript.getScript());
		final Term equalsReplacement = mdsos.constructEqualsReplacement();
		final Term notEquasReplacement = mdsos.constructNotEqualsReplacement(mgdScript.getScript());
		return Util.ite(mgdScript.getScript(), eq, equalsReplacement, notEquasReplacement);
	}
	

}
