/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Provide information for the questions which Terms are equivalent at a given location.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public interface IEqualityAnalysisResultProvider<LOC, CFG> {

	EqualityAnalysisResult getAnalysisResult(LOC location, Set<Doubleton<Term>> doubletons);

	/**
	 * Announce to the analysis that all the given constants are pairwise distinct (like literals are).
	 *
	 * @param collection constants to announce as literals.
	 */
	void announceAdditionalLiterals(Collection<IProgramConst> collection);

	void preprocess(CFG cfg);

	IEqualityProvidingState getEqualityProvidingStateForLocationSet(Set<IcfgLocation> arrayGroupAccessLocations);

	IEqualityProvidingIntermediateState getEqualityProvidingIntermediateState(IcfgEdge edge);

	/**
	 * only these arrays are tracked "intensively" i.e. using weak equivalences
	 * @param trackedArrays
	 */
	void setTrackedArrays(List<String> trackedArrays);

}
