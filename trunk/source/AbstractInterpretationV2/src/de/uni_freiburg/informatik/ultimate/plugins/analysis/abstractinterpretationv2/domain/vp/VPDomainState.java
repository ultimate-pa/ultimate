/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of an abstract state of the {@link VPDomain}.
 * 
 * <p>
 * Such a state stores {@link VPDomainValue}s.
 * </p>
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 * @param <ACTION>
 *            Any action.
 * @param <IBoogieVar>
 *            Any variable declaration.
 */
public class VPDomainState implements IAbstractState<VPDomainState, CodeBlock, IBoogieVar> {

	private static int sId;
	private final int mId;

	private final Set<IBoogieVar> mVariables;
	private final Map<String, Set<Expression>> mVarExprMap;
	private final Set<Expression> mExprSet;
	private final Map<String, Set<Expression>> mPtrReadintMap;

	private final boolean mIsFixpoint;

	protected VPDomainState() {
		mVariables = new HashSet<>();
		mVarExprMap = new HashMap<String, Set<Expression>>();
		mExprSet = new HashSet<Expression>();
		mPtrReadintMap = new HashMap<String, Set<Expression>>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
	}

	protected VPDomainState(final Set<IBoogieVar> variablesMap, final Map<String, Set<Expression>> varExprMap,
			final Set<Expression> exprSet, final Map<String, Set<Expression>> ptrReadintMap, final boolean isFixpoint) {
		mVariables = variablesMap;
		mVarExprMap = new HashMap<String, Set<Expression>>(varExprMap);
		mExprSet = new HashSet<Expression>(exprSet);
		mPtrReadintMap = new HashMap<String, Set<Expression>>(ptrReadintMap);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
	}

	public Map<String, Set<Expression>> getPtrReadintMap() {
		return mPtrReadintMap;
	}

	public Set<Expression> getExprSet() {
		return mExprSet;
	}

	public Map<String, Set<Expression>> getVarExprMap() {
		return mVarExprMap;
	}

	@Override
	public VPDomainState addVariable(final IBoogieVar variable) {
		assert variable != null;

		final Set<IBoogieVar> newVarMap = new HashSet<>(mVariables);
		if (!newVarMap.add(variable)) {
			throw new UnsupportedOperationException("Variable names must be disjoint.");
		}
		return new VPDomainState(newVarMap, mVarExprMap, mExprSet, mPtrReadintMap, mIsFixpoint);
	}

	@Override
	public VPDomainState removeVariable(final IBoogieVar variable) {
		assert variable != null;
		final Set<IBoogieVar> newVarMap = new HashSet<>(mVariables);
		newVarMap.remove(variable);
		return new VPDomainState(newVarMap, mVarExprMap, mExprSet, mPtrReadintMap, mIsFixpoint);
	}

	@Override
	public VPDomainState addVariables(final Collection<IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Set<IBoogieVar> newVarMap = new HashSet<IBoogieVar>(mVariables);

		for (final IBoogieVar entry : variables) {
			if (!newVarMap.add(entry)) {
				throw new UnsupportedOperationException("Variable names must be disjoint.");
			}
		}

		return new VPDomainState(newVarMap, mVarExprMap, mExprSet, mPtrReadintMap, mIsFixpoint);
	}

	@Override
	public VPDomainState removeVariables(final Collection<IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Set<IBoogieVar> newVarMap = new HashSet<IBoogieVar>(mVariables);
		return new VPDomainState(newVarMap, mVarExprMap, mExprSet, mPtrReadintMap, mIsFixpoint);
	}

	@Override
	public boolean containsVariable(final IBoogieVar var) {
		return mVariables.contains(var);
	}

	@Override
	public boolean isEmpty() {
		return mVariables.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	public VPDomainState setFixpoint(final boolean value) {
		return new VPDomainState(mVariables, mVarExprMap, mExprSet, mPtrReadintMap, value);
	}

	/**
	 * Build a string of the form "var1 : type1 = value1; var2 : type2 = value2; ...".
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuffer = new StringBuilder();
		for (final Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			stringBuffer.append(entry.getKey()).append(':').append(entry.getValue()).append(" = ")
					.append(mVarExprMap.get(entry.getKey()).toString()).append("; ");

		}
		return stringBuffer.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public int hashCode() {
		return mId;
	}

	@Override
	public boolean equals(final Object other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (this.getClass() != other.getClass()) {
			return false;
		}

		return isEqualTo((VPDomainState) other);
	}

	@Override
	public boolean isEqualTo(final VPDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}
		for (final Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			final Set<Expression> otherValue = other.getExpressionMap().get(entry.getKey());
			if (!mVarExprMap.get(entry.getKey()).equals(otherValue)) {
				return false;
			}
		}
		return true;
	}

	protected boolean hasSameVariables(final VPDomainState other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof VPDomainState)) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		if (other.mVariables.size() != mVariables.size()) {
			return false;
		}

		for (final IBoogieVar entry : mVariables) {
			if (!other.mVariables.contains(entry)) {
				return false;
			}
		}

		return true;
	}

	public VPDomainState copy() {

		final Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>();
		for (final Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			final String key = entry.getKey();
			newExprMap.put(key, new HashSet<Expression>(mVarExprMap.get(key)));
		}

		final Map<String, Set<Expression>> newPtrReadinMap = new HashMap<String, Set<Expression>>();
		for (final Entry<String, Set<Expression>> entry : mPtrReadintMap.entrySet()) {
			final String key = entry.getKey();
			newPtrReadinMap.put(key, new HashSet<Expression>(mPtrReadintMap.get(key)));
		}

		return new VPDomainState(new HashSet<IBoogieVar>(mVariables), newExprMap, new HashSet<Expression>(mExprSet),
				newPtrReadinMap, mIsFixpoint);
	}

	@Override
	public Set<IBoogieVar> getVariables() {
		return Collections.unmodifiableSet(mVariables);
	}

	protected Map<String, Set<Expression>> getExpressionMap() {
		return new HashMap<String, Set<Expression>>(mVarExprMap);
	}

	protected void setExpressionMap(final Map<String, Set<Expression>> exprMap) {

		assert exprMap != null;

		mVarExprMap.clear();

		for (final Entry<String, Set<Expression>> entry : exprMap.entrySet()) {
			mVarExprMap.put(entry.getKey(), entry.getValue());
		}
	}

	protected void setExpressionSet(final Set<Expression> exprSet) {

		assert exprSet != null;
		mExprSet.clear();
		mExprSet.addAll(exprSet);
	}

	protected void setPtrReadinMap(final Map<String, Set<Expression>> ptrReadinMap) {

		assert ptrReadinMap != null;

		mPtrReadintMap.clear();

		for (final Entry<String, Set<Expression>> entry : ptrReadinMap.entrySet()) {
			mPtrReadintMap.put(entry.getKey(), entry.getValue());
		}
	}

	public void printExprMap() {
		System.out.println(" Variables Expression Map: ");
		for (final Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			if (entry.getValue() instanceof IntegerLiteral) {
				System.out.println(entry.getKey() + ": " + ((IntegerLiteral) entry.getValue()).getValue());
			} else {
				System.out.println(entry.getKey() + ": " + entry.getValue().toString());
			}

		}
	}

	public void printPtrReadintMap() {
		System.out.println(" Pointer Read-int Map: ");
		for (final Entry<String, Set<Expression>> entry : mPtrReadintMap.entrySet()) {
			if (entry.getValue() instanceof IntegerLiteral) {
				System.out.println(entry.getKey() + ": " + ((IntegerLiteral) entry.getValue()).getValue());
			} else {
				System.out.println(entry.getKey() + ": " + entry.getValue().toString());
			}

		}
	}

	@Override
	public Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
		return script.term("true");
	}

	@Override
	public VPDomainState patch(final VPDomainState dominator) {
		return dominator;
	}

	/**
	 * Generate the variables grouping information from the partition. Return map key: variable name. value: group.
	 * 
	 * @param partition
	 * @return the variables grouping information
	 */
	public static Map<String, String> generateVarGroupInfo(final Map<String, Set<String>> partition) {

		final Iterator<String> partitionIter = partition.keySet().iterator();
		String groupNumber;
		Set<String> groupSet;
		Iterator<String> groupSetIter;

		final Map<String, String> result = new HashMap<String, String>();

		while (partitionIter.hasNext()) {
			groupNumber = partitionIter.next();
			groupSet = partition.get(groupNumber);
			groupSetIter = groupSet.iterator();

			while (groupSetIter.hasNext()) {
				result.put(groupSetIter.next(), groupNumber);
			}
		}
		return result;
	}

	/**
	 * Re-index the partition group, in case there's a whole group that had been remove, and that index will be skip.
	 * 
	 * @param partition
	 *            to be sorted out.
	 * @return a new partition map that no index is skipped.
	 */
	public static Map<String, Set<String>> reIndexGroups(final Map<String, Set<String>> partition) {

		final Map<String, Set<String>> result = new HashMap<String, Set<String>>();

		final Set<String> keySet = partition.keySet();
		final Iterator<String> keySetIter = keySet.iterator();
		int index = 1;
		String key;

		while (keySetIter.hasNext()) {
			key = keySetIter.next();
			if (partition.get(key).isEmpty()) {
				continue;
			}
			result.put(Integer.toString(index), partition.get(key));
			index++;
		}

		return result;
	}

	public static String getNextIndex(final Map<String, Set<String>> partition) {

		if (partition.isEmpty()) {
			return "1";
		}

		final Set<String> keySet = partition.keySet();
		final Iterator<String> keySetIter = keySet.iterator();

		int max = Integer.parseInt(keySetIter.next());

		while (keySetIter.hasNext()) {
			final int next = Integer.parseInt(keySetIter.next());
			if (max < next) {
				max = next;
			}
		}
		return Integer.toString(max + 1);
	}

	@Override
	public SubsetResult isSubsetOf(final VPDomainState other) {
		assert hasSameVariables(other);
		return isEqualTo(other) ? SubsetResult.EQUAL : SubsetResult.NONE;
	}
}
