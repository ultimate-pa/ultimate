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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class SegmentationMap {
	private final UnionFind<IProgramVarOrConst> mEqualArrays;
	private final Map<IProgramVarOrConst, Segmentation> mRepresentiveSegmentations;

	private SegmentationMap(final UnionFind<IProgramVarOrConst> equalArrays,
			final Map<IProgramVarOrConst, Segmentation> representiveSegmentations) {
		mEqualArrays = equalArrays;
		mRepresentiveSegmentations = representiveSegmentations;
	}

	public SegmentationMap() {
		this(new UnionFind<>(), new HashMap<>());
	}

	public SegmentationMap(final SegmentationMap map) {
		this(map.mEqualArrays.clone(), new HashMap<>(map.mRepresentiveSegmentations));
	}

	public Set<IProgramVarOrConst> getArrays() {
		return mEqualArrays.getAllElements();
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
		mEqualArrays.makeEquivalenceClass(variable);
		mRepresentiveSegmentations.put(variable, segmentation);
	}

	public void addEquivalenceClass(final Set<IProgramVarOrConst> variables, final Segmentation segmentation) {
		mEqualArrays.addEquivalenceClass(variables);
		final IProgramVarOrConst var = variables.iterator().next();
		mRepresentiveSegmentations.put(mEqualArrays.find(var), segmentation);
	}

	public void addAll(final SegmentationMap other) {
		for (final IProgramVarOrConst rep : other.mEqualArrays.getAllRepresentatives()) {
			mEqualArrays.addEquivalenceClass(other.getEquivalenceClass(rep), rep);
			mRepresentiveSegmentations.put(rep, other.getSegmentation(rep));
		}
	}

	public void renameArray(final IProgramVarOrConst oldVar, final IProgramVarOrConst newVar) {
		final IProgramVarOrConst rep = mEqualArrays.find(oldVar);
		final boolean isSingleton = mEqualArrays.getEquivalenceClassMembers(oldVar).size() == 1;
		mEqualArrays.remove(oldVar);
		mEqualArrays.makeEquivalenceClass(newVar);
		final Segmentation segmentation = mRepresentiveSegmentations.get(oldVar);
		if (segmentation == null) {
			mEqualArrays.union(newVar, rep);
		} else {
			mRepresentiveSegmentations.remove(oldVar);
			if (!isSingleton) {
				mEqualArrays.union(newVar, rep);
			}
			mRepresentiveSegmentations.put(mEqualArrays.find(newVar), segmentation);
		}
	}

	public void put(final IProgramVarOrConst variable, final Segmentation newSegmentation) {
		final IProgramVarOrConst rep = mEqualArrays.find(variable);
		mRepresentiveSegmentations.put(rep, newSegmentation);
	}

	public void remove(final IProgramVarOrConst variable) {
		mEqualArrays.remove(variable);
	}

	public void move(final IProgramVarOrConst variable, final IProgramVarOrConst target) {
		remove(variable);
		mEqualArrays.makeEquivalenceClass(variable);
		mEqualArrays.union(variable, target);
	}

	public void union(final IProgramVarOrConst var1, final IProgramVarOrConst var2, final Segmentation segmentation) {
		mRepresentiveSegmentations.remove(mEqualArrays.find(var1));
		mRepresentiveSegmentations.remove(mEqualArrays.find(var2));
		mEqualArrays.union(var1, var2);
		mRepresentiveSegmentations.put(mEqualArrays.find(var1), segmentation);
	}

	@Override
	public String toString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final Entry<IProgramVarOrConst, Segmentation> entry : mRepresentiveSegmentations.entrySet()) {
			stringBuilder.append(mEqualArrays.getEquivalenceClassMembers(entry.getKey()));
			stringBuilder.append(" -> ").append(entry.getValue()).append(' ');
		}
		return stringBuilder.toString();
	}

	public boolean isEmpty() {
		return mRepresentiveSegmentations.isEmpty();
	}

	public Segmentation getSegmentation(final IProgramVarOrConst variable) {
		return mRepresentiveSegmentations.get(mEqualArrays.find(variable));
	}

	public Set<IProgramVarOrConst> getEquivalenceClass(final IProgramVarOrConst variable) {
		return mEqualArrays.getEquivalenceClassMembers(variable);
	}

	// TODO: Different segmentations can share value-variables, how to handle this?
	public Term getTerm(final ManagedScript managedScript, final Term valueConstraints) {
		final Script script = managedScript.getScript();
		final List<Term> conjuncts = new ArrayList<>();
		final List<Term> boundConstraints = new ArrayList<>();
		final Set<TermVariable> bounds = new HashSet<>();
		final Map<Term, Term> substitution = new HashMap<>();
		for (final Entry<IProgramVarOrConst, Segmentation> entry : mRepresentiveSegmentations.entrySet()) {
			final IProgramVarOrConst rep = entry.getKey();
			final Segmentation segmentation = entry.getValue();
			final Term repVar = NonrelationalTermUtils.getTermVar(rep);
			for (final IProgramVarOrConst eq : getEquivalenceClass(rep)) {
				conjuncts.add(SmtUtils.binaryEquality(script, repVar, NonrelationalTermUtils.getTermVar(eq)));
			}
			final Sort arraySort = rep.getSort();
			final Sort boundSort = TypeUtils.getIndexSort(arraySort);
			for (int i = 0; i < segmentation.size(); i++) {
				final TermVariable idx = managedScript.constructFreshTermVariable("idx", boundSort);
				final Term prev = NonrelationalTermUtils.getTermVar(segmentation.getBound(i));
				final Term next = NonrelationalTermUtils.getTermVar(segmentation.getBound(i + 1));
				if (i > 0) {
					boundConstraints.add(SmtUtils.leq(script, prev, idx));
				}
				if (i < segmentation.size() - 1) {
					boundConstraints.add(SmtUtils.less(script, idx, next));
				}
				bounds.add(idx);
				final Term value = NonrelationalTermUtils.getTermVar(segmentation.getValue(i));
				final Term select = script.term("select", repVar, idx);
				substitution.put(value, select);

			}
		}
		final Term substituted = new Substitution(script, substitution).transform(valueConstraints);
		final Term body = Util.implies(script, SmtUtils.and(script, boundConstraints), substituted);
		final Term quntified = SmtUtils.quantifier(script, QuantifiedFormula.FORALL, bounds, body);
		conjuncts.add(quntified);
		return SmtUtils.and(script, conjuncts);
	}
}
