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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
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
 *
 * @param <ACTION>
 *            Any action.
 * @param <IBoogieVar>
 *            Any variable declaration.
 */
public class VPDomainState implements IAbstractState<VPDomainState, CodeBlock, IBoogieVar> {

	private static int sId;
	private final int mId;

	private final Map<String, IBoogieVar> mVariablesMap;
	private final Map<String, Set<Expression>> mVarExprMap;
	private final Set<Expression> mExprSet;

	private boolean mIsFixpoint;

	protected VPDomainState() {
		mVariablesMap = new HashMap<String, IBoogieVar>();
		mVarExprMap = new HashMap<String, Set<Expression>>();
		mExprSet = new HashSet<Expression>();
		mIsFixpoint = false;
		sId++;
		mId = sId;
	}

	protected VPDomainState(Map<String, IBoogieVar> variablesMap,
			Map<String, Set<Expression>> varExprMap, Set<Expression> exprSet,
			boolean isFixpoint) {
		mVariablesMap = new HashMap<String, IBoogieVar>(variablesMap);
		mVarExprMap = new HashMap<String, Set<Expression>>(varExprMap);
		mExprSet = new HashSet<Expression>(exprSet);
		mIsFixpoint = isFixpoint;
		sId++;
		mId = sId;
	}
	
	public Set<Expression> getExprSet() {
		return mExprSet;
	}

	public Map<String, Set<Expression>> getVarExprMap() {
		return mVarExprMap;
	}

	public Set<String> getVariablesSet() {
		return mVariablesMap.keySet();
	}

	@Override
	public VPDomainState addVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(
				mVariablesMap);
		final IBoogieVar old = newVarMap.put(name, variable);
		if (old != null) {
			throw new UnsupportedOperationException(
					"Variable names must be disjoint.");
		}

		final Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>(
				mVarExprMap);

		newExprMap.put(name, new HashSet<Expression>());

		return new VPDomainState(newVarMap, newExprMap, mExprSet, mIsFixpoint);
	}

	@Override
	public VPDomainState removeVariable(String name, IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(
				mVariablesMap);
//		newVarMap.remove(name);
		final Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>(
				mVarExprMap);

//		newExprMap.remove(name);

		return new VPDomainState(newVarMap, newExprMap, mExprSet, mIsFixpoint);
	}

	@Override
	public VPDomainState addVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(
				mVariablesMap);
		final Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>(
				mVarExprMap);

		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			final IBoogieVar old = newVarMap.put(entry.getKey(),
					entry.getValue());
			if (old != null) {
				throw new UnsupportedOperationException(
						"Variable names must be disjoint.");
			}
			newExprMap.put(entry.getKey(), new HashSet<Expression>());
		}

		return new VPDomainState(newVarMap, newExprMap, mExprSet, mIsFixpoint);
	}

	@Override
	public VPDomainState removeVariables(Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(
				mVariablesMap);
		final Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>(
				mVarExprMap);

//		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
//			newVarMap.remove(entry.getKey());
//			newExprMap.remove(entry.getKey());
//		}

		return new VPDomainState(newVarMap, newExprMap, mExprSet, mIsFixpoint);
	}

	@Override
	public boolean containsVariable(String name) {
		return mVariablesMap.containsKey(name);
	}

	@Override
	public boolean isEmpty() {
		return mVariablesMap.isEmpty();
	}

	@Override
	public boolean isBottom() {
//		for (final Entry<String, VPDomainValue> entry : mValuesMap.entrySet()) {
//			if (entry.getValue().getResult() == Values.BOTTOM) {
//				return true;
//			}
//		}
		return false;
	}

	public boolean isFixpoint() {
		return mIsFixpoint;
	}

	public VPDomainState setFixpoint(boolean value) {
		return new VPDomainState(mVariablesMap, mVarExprMap, mExprSet, value);
	}

	/**
	 * Build a string of the form
	 * "var1 : type1 = value1; var2 : type2 = value2; ...".
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuffer = new StringBuilder();
		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			stringBuffer.append(entry.getKey()).append(':')
					.append(entry.getValue()).append(" = ")
					.append(mVarExprMap.get(entry.getKey()).toString())
					.append("; ");
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
	public boolean equals(Object other) {
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
	public boolean isEqualTo(VPDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}
		for (final Entry<String, Set<Expression>> entry : mVarExprMap
				.entrySet()) {
			final Set<Expression> otherValue = other.getExpressionMap().get(entry
					.getKey());
			if (!mVarExprMap.get(entry.getKey()).equals(otherValue)) {
				return false;
			}
		}
		return true;
	}

	protected boolean hasSameVariables(VPDomainState other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof VPDomainState)) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		if (other.mVariablesMap.size() != mVariablesMap.size()) {
			return false;
		}

		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			final IBoogieVar otherType = other.mVariablesMap.get(entry.getKey());
			if (!entry.getValue().equals(otherType)) {
				return false;
			}
		}

		return true;
	}

	public VPDomainState copy() {
		
		Map<String, Set<Expression>> newExprMap = new HashMap<String, Set<Expression>>();
		
		for (final Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			final String key = entry.getKey();
			newExprMap.put(key, new HashSet<Expression>(mVarExprMap.get(key)));
		}
		
		return new VPDomainState(
				new HashMap<String, IBoogieVar>(mVariablesMap),
				newExprMap, 
				new HashSet<Expression>(mExprSet),
				mIsFixpoint);
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mVariablesMap);
	}

	protected Map<String, Set<Expression>> getExpressionMap() {
		return new HashMap<String, Set<Expression>>(mVarExprMap);
	}

	protected void setExpressionMap(Map<String, Set<Expression>> exprMap) {

		assert exprMap != null;
		// assert mVariablesMap.containsKey(name);
		// assert mVarPartitionMap.containsKey(name);

		mVarExprMap.clear();

		for (final Entry<String, Set<Expression>> entry : exprMap.entrySet()) {
			mVarExprMap.put(entry.getKey(), entry.getValue());
		}
	}
	
	protected void setExpressionSet(Set<Expression> exprSet) {

		assert exprSet != null;
		mExprSet.clear();
		mExprSet.addAll(exprSet);
	}
	
	public void printExprMap() {
		System.out.println(" Variables Expression Map: ");
		for (Entry<String, Set<Expression>> entry : mVarExprMap.entrySet()) {
			if (entry.getValue() instanceof IntegerLiteral) {
				System.out.println(entry.getKey() + ": "
						+ ((IntegerLiteral) entry.getValue()).getValue());
			} else {
				System.out.println(entry.getKey() + ": "
						+  entry.getValue().toString());
			}

		}
	}

	/**
	 * Intersects {@link this} with another {@link VPDomainState} by intersecting each value of each variable.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new state which corresponds to the intersection.
	 */
//	protected VPDomainState intersect(VPDomainState other) {
//		assert hasSameVariables(other);
//
//		final VPDomainState newState = (VPDomainState) this.copy();
//
//		for (final Entry<String, IBoogieVar> variable : mVariablesMap.entrySet()) {
//			final String key = variable.getKey();
//			newState.setValue(key, mValuesMap.get(key).intersect(other.mValuesMap.get(key)));
//		}
//
//		return newState;
//	}

//	public void setToBottom() {
//		for (final Entry<String, VPDomainValue> entry : mValuesMap.entrySet()) {
//			entry.setValue(new VPDomainValue(Values.BOTTOM));
//		}
//	}

	@Override
	public Term getTerm(Script script, Boogie2SMT bpl2smt) {
		return script.term("true");
	}

//	@Override
//	public IBoogieVar getVariableType(String name) {
//		assert name != null;
//		assert mVariablesMap.containsKey(name);
//
//		return mVariablesMap.get(name);
//	}

	@Override
	public VPDomainState patch(final VPDomainState dominator) {
//		throw new UnsupportedOperationException("not yet implemented");
		// TODO
		return dominator;
	}
	
	/**
	 * Generate the variables grouping information from the partition. Return
	 * map key: variable name. value: group.
	 * 
	 * @param partition
	 * @return the variables grouping information
	 */
	public static Map<String, String> generateVarGroupInfo(
			Map<String, Set<String>> partition) {

		Iterator<String> partitionIter = partition.keySet().iterator();
		String groupNumber;
		Set<String> groupSet;
		Iterator<String> groupSetIter;

		Map<String, String> result = new HashMap<String, String>();

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

	// public void putToSameGroup(String identifier1, String identifier2) {
	// Map<String, String> groupInfo = generateVarGroupInfo(mVarPartitionMap);
	//
	// String group1 = groupInfo.get(identifier1);
	// String group2 = groupInfo.get(identifier2);
	//
	// if (!group1.equals(group2)) {
	//
	// mVarPartitionMap.get(group1).addAll(mVarPartitionMap.get(group2));
	// mVarPartitionMap.remove(group2);
	// reIndexGroups(mVarPartitionMap);
	// }
	// }

	/**
	 * Re-index the partition group, in case there's a whole group that had been
	 * remove, and that index will be skip.
	 * 
	 * @param partition
	 *            to be sorted out.
	 * @return a new partition map that no index is skipped.
	 */
	public static Map<String, Set<String>> reIndexGroups(
			Map<String, Set<String>> partition) {

		Map<String, Set<String>> result = new HashMap<String, Set<String>>();

		Set<String> keySet = partition.keySet();
		Iterator<String> keySetIter = keySet.iterator();
		int index = 1;
		String key;

		while (keySetIter.hasNext()) {
			key = keySetIter.next();
			if (partition.get(key).isEmpty()) {
				continue;
			}
			result.put(new Integer(index).toString(), partition.get(key));
			index++;
		}

		return result;
	}

	public static String getNextIndex(Map<String, Set<String>> partition) {

		if (partition.isEmpty()) {
			return "1";
		}

		Set<String> keySet = partition.keySet();
		Iterator<String> keySetIter = keySet.iterator();

		Integer max = new Integer(keySetIter.next());
		String next;

		while (keySetIter.hasNext()) {
			next = keySetIter.next();
			if (max.compareTo(new Integer(next)) < 0) {
				max = new Integer(next);
			}
			// indexList.add(new Integer(keySetIter.next()));
		}

		// Collections.sort(indexList);
		// int maxIndex = indexList.get(indexList.size()).intValue();
		// Integer result = new Integer(maxIndex + 1);

		return new Integer((max.intValue() + 1)).toString();
	}

	@Override
	public IBoogieVar getVariableDeclarationType(String name) {
		// TODO Auto-generated method stub
		return null;
	}
	
//	public static Map<String, Set<Expression>> calculateGlobleExprMap(List<VPDomainState> states) {
//		
//		Map<String, Set<Expression>> resultExprMap = new HashMap<String, Set<Expression>>();
//		
//		for (VPDomainState state : states) {
//			
//		}
//		
//		return ;
//	}

	// public static Map<String, Set<String>> join(VPDomainState domain1,
	// VPDomainState domain2) {
	//
	// Set<String> vars1 = domain1.getVariablesSet();
	// Set<String> vars2 = domain2.getVariablesSet();
	// Map<String, Set<String>> partition1 = domain1.getPartition();
	// Map<String, Set<String>> partition2 = domain2.getPartition();
	//
	// Iterator<String> varIterator1 = vars1.iterator();
	//
	// Map<String, String> partitionInfo1 =
	// VPDomainState.generateVarGroupInfo(partition1);
	// Map<String, String> partitionInfo2 =
	// VPDomainState.generateVarGroupInfo(partition2);
	//
	// String x;
	// String y;
	//
	// List<String> pairList = new ArrayList<String>();
	//
	// while (varIterator1.hasNext()) {
	// x = varIterator1.next();
	// Iterator<String> varIterator2 = vars2.iterator();
	// while (varIterator2.hasNext()) {
	// y = varIterator2.next();
	//
	// if (!x.equals(y)) {
	// // if x and y are in the same partition, no matter it's from
	// // partition 1 or 2, then put them into same group.
	// if ((!partitionInfo1.get(x).equals(partitionInfo1.get(y)))
	// && (partitionInfo2.get(x).equals(partitionInfo2
	// .get(y)))) {
	// pairList.add(new String(x + "," + y));
	// }
	// }
	// }
	// }
	//
	// String g;
	// String v;
	// for (String p : pairList) {
	//
	// String[] pair = p.split(",");
	//
	// String xGroup = partitionInfo1.get(pair[0]);
	// String yGroup = partitionInfo2.get(pair[1]);
	//
	// if (partition1.containsKey(xGroup)) {
	// partition1.get(xGroup).addAll(partition2.get(yGroup));
	//
	// Iterator<String> p2SetIter = partition2.get(yGroup).iterator();
	// while (p2SetIter.hasNext()) {
	// v = p2SetIter.next();
	// g = partitionInfo1.get(v);
	// if (g == null) {
	// continue;
	// }
	// if (!g.equals(xGroup)) {
	// if (partition1.containsKey(g)) {
	// partition1.get(xGroup).addAll(partition1.get(g));
	// partition1.remove(g);
	// }
	//
	// }
	// }
	// }
	// }
	//
	// /*
	// * If there's a whole group in partition2, that the elements in it are
	// * not in partition1, then add the group into partition1. The following
	// * are dealt with this situation.
	// */
	//
	// // because the process above may remove a whole group from partition1,
	// // so call sortOutPartition to sort the partition out.
	// partition1 = reIndexGroups(partition1);
	// Map<String, String> newPartition1Info =
	// VPDomainState.generateVarGroupInfo(partition1);
	//
	// Set<String> par2KeySet = partition2.keySet();
	// Iterator<String> par2KeySetIter = par2KeySet.iterator();
	// String par2KeySetIterGroup;
	//
	// Set<String> par2VarSet;
	// Iterator<String> par2VarSetIter;
	// String par2VarSetIterElement;
	//
	// while (par2KeySetIter.hasNext()) {
	// par2KeySetIterGroup = par2KeySetIter.next();
	//
	// par2VarSet = partition2.get(par2KeySetIterGroup);
	// par2VarSetIter = par2VarSet.iterator();
	//
	// boolean isNotInPar1 = true;
	//
	// while (par2VarSetIter.hasNext()) {
	// par2VarSetIterElement = par2VarSetIter.next();
	// isNotInPar1 = (!newPartition1Info
	// .containsKey(par2VarSetIterElement)) && isNotInPar1;
	// }
	//
	// if (isNotInPar1) {
	// int size = partition1.size();
	// partition1.put(new Integer(size + 1).toString(), par2VarSet);
	// }
	// }
	// return partition1;
	// }
}
