/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class SegmentationMap {
	private final UnionFind<IProgramVarOrConst> mArrayEqualities;
	private final Map<IProgramVarOrConst, Segmentation> mRepresentiveSegmentations;

	private SegmentationMap(final UnionFind<IProgramVarOrConst> arrayEqualities,
			final Map<IProgramVarOrConst, Segmentation> representiveSegmentations) {
		mArrayEqualities = arrayEqualities;
		mRepresentiveSegmentations = representiveSegmentations;
	}

	public SegmentationMap() {
		this(new UnionFind<>(), new HashMap<>());
	}

	public SegmentationMap(final SegmentationMap map) {
		this(map.mArrayEqualities.clone(), new HashMap<>(map.mRepresentiveSegmentations));
	}

	public Set<IProgramVarOrConst> getArrays() {
		return mArrayEqualities.getAllElements();
	}

	public Set<IProgramVar> getValueVars() {
		final Set<IProgramVar> variables = new HashSet<>();
		for (final Segmentation s : mRepresentiveSegmentations.values()) {
			variables.addAll(s.getValues());
		}
		return variables;
	}

	public Set<IProgramVar> getBoundVars() {
		final Set<IProgramVar> variables = new HashSet<>();
		for (final Segmentation s : mRepresentiveSegmentations.values()) {
			variables.addAll(s.getBounds());
		}
		return variables;
	}

	public Set<IProgramVar> getAuxVars() {
		final Set<IProgramVar> variables = new HashSet<>();
		variables.addAll(getBoundVars());
		variables.addAll(getValueVars());
		return variables;
	}

	public void add(final IProgramVarOrConst variable, final Segmentation segmentation) {
		mArrayEqualities.makeEquivalenceClass(variable);
		mRepresentiveSegmentations.put(variable, segmentation);
	}

	public void addEquivalenceClass(final Set<IProgramVarOrConst> variables, final Segmentation segmentation) {
		mArrayEqualities.addEquivalenceClass(variables);
		final IProgramVarOrConst var = variables.iterator().next();
		mRepresentiveSegmentations.put(mArrayEqualities.find(var), segmentation);
	}

	public void putAll(final SegmentationMap other) {
		for (final IProgramVarOrConst rep : other.mArrayEqualities.getAllRepresentatives()) {
			final Set<IProgramVarOrConst> eqClass = other.getEquivalenceClass(rep);
			for (final IProgramVarOrConst v : eqClass) {
				if (getArrays().contains(v)) {
					remove(v);
				}
			}
			mArrayEqualities.addEquivalenceClass(eqClass, rep);
			mRepresentiveSegmentations.put(rep, other.getSegmentation(rep));
		}
	}

	public void renameArray(final IProgramVarOrConst oldVar, final IProgramVarOrConst newVar) {
		final IProgramVarOrConst rep = mArrayEqualities.find(oldVar);
		final boolean isSingleton = mArrayEqualities.getEquivalenceClassMembers(oldVar).size() == 1;
		mArrayEqualities.remove(oldVar);
		mArrayEqualities.makeEquivalenceClass(newVar);
		final Segmentation segmentation = mRepresentiveSegmentations.get(oldVar);
		if (segmentation == null) {
			mArrayEqualities.union(newVar, rep);
		} else {
			mRepresentiveSegmentations.remove(oldVar);
			if (!isSingleton) {
				mArrayEqualities.union(newVar, rep);
			}
			mRepresentiveSegmentations.put(mArrayEqualities.find(newVar), segmentation);
		}
	}

	public void put(final IProgramVarOrConst variable, final Segmentation newSegmentation) {
		final IProgramVarOrConst rep = mArrayEqualities.find(variable);
		mRepresentiveSegmentations.put(rep, newSegmentation);
	}

	public void remove(final IProgramVarOrConst variable) {
		final Set<IProgramVarOrConst> newEquivalenceClass = new HashSet<>(mArrayEqualities.getContainingSet(variable));
		newEquivalenceClass.remove(variable);
		final Iterator<IProgramVarOrConst> iterator = newEquivalenceClass.iterator();
		mArrayEqualities.remove(variable);
		final Segmentation segmentation = mRepresentiveSegmentations.remove(variable);
		if (segmentation != null && iterator.hasNext()) {
			mRepresentiveSegmentations.put(mArrayEqualities.find(iterator.next()), segmentation);
		}
	}

	public void removeAll(final Set<IProgramVarOrConst> variables) {
		for (final IProgramVarOrConst v : variables) {
			remove(v);
		}
	}

	public void move(final IProgramVarOrConst variable, final IProgramVarOrConst target) {
		if (mArrayEqualities.find(variable) != null) {
			remove(variable);
		}
		mArrayEqualities.makeEquivalenceClass(variable);
		mArrayEqualities.union(variable, target);
	}

	public void union(final IProgramVarOrConst var1, final IProgramVarOrConst var2, final Segmentation segmentation) {
		mRepresentiveSegmentations.remove(mArrayEqualities.find(var1));
		mRepresentiveSegmentations.remove(mArrayEqualities.find(var2));
		mArrayEqualities.union(var1, var2);
		mRepresentiveSegmentations.put(mArrayEqualities.find(var1), segmentation);
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		stringBuilder.append('{');
		for (final IProgramVarOrConst rep : sortProgramVars(getAllRepresentatives())) {
			stringBuilder.append(sortProgramVars(mArrayEqualities.getEquivalenceClassMembers(rep)));
			stringBuilder.append(" -> ").append(mRepresentiveSegmentations.get(rep)).append(", ");
		}
		stringBuilder.append('}');
		return stringBuilder.toString();
	}

	private static List<IProgramVarOrConst> sortProgramVars(final Collection<IProgramVarOrConst> programVars) {
		return programVars.stream().sorted((x, y) -> x.toString().compareTo(y.toString())).collect(Collectors.toList());
	}

	public Segmentation getSegmentation(final IProgramVarOrConst variable) {
		return mRepresentiveSegmentations.get(mArrayEqualities.find(variable));
	}

	public Set<IProgramVarOrConst> getEquivalenceClass(final IProgramVarOrConst variable) {
		return mArrayEqualities.getEquivalenceClassMembers(variable);
	}

	public Collection<IProgramVarOrConst> getAllRepresentatives() {
		return mArrayEqualities.getAllRepresentatives();
	}
}
