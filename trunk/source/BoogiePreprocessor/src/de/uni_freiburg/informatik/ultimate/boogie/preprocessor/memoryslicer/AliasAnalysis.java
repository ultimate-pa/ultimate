/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AliasAnalysis {

	private final AddressStoreFactory mAsfac;
//	private final MayAlias mMa = new MayAlias();
	private final Set<PointerBase> mWriteAddresses;
	private final Set<PointerBase> mAccessAddresses;


	public AliasAnalysis(final AddressStoreFactory asfac) {
		super();
		mAsfac = asfac;
		mWriteAddresses = new HashSet<>();
		mAccessAddresses = new HashSet<>();
	}



	public Set<PointerBase> getWriteAddresses() {
		return mWriteAddresses;
	}



	public Set<PointerBase> getAccessAddresses() {
		return mAccessAddresses;
	}



	public MayAlias aliasAnalysis(final Unit unit) {
			for (final Declaration d : unit.getDeclarations()) {
				if (d instanceof Procedure) {
					final Procedure p = (Procedure) d;
					if (p.getBody() != null) {
						final MayAlias mas2 = processBody2(p.getBody());
						return mas2;
					}
				}
			}
		throw new AssertionError("Analysis failed");
	}


	private MayAlias processBody2(final Body body) {
		final MayAlias mas = new MayAlias();
		for (final Statement st : body.getBlock()) {
			if (st instanceof GotoStatement) {
				// do nothing
			} else if (st instanceof Label) {
				// do nothing
			} else if (st instanceof CallStatement) {
				processCallStatement(mas, (CallStatement) st);
			} else if (st instanceof AssignmentStatement) {
				processAssignmentStatement(mas, (AssignmentStatement) st);
			} else if (st instanceof AssumeStatement) {
				processAssumeStatement(mas, (AssumeStatement) st);
			} else if (st instanceof AssertStatement) {
				processAssertStatement(mas, (AssertStatement) st);
			} else if (st instanceof HavocStatement) {
				processHavocStatement(mas, (HavocStatement) st);
			} else if (st instanceof ReturnStatement) {
				// do nothing
			} else {
				throw new AssertionError("Unsuppored " + st);
			}
		}
		return mas;
	}

	private MayAlias processHavocStatement(final MayAlias currentState, final HavocStatement st) {
		return currentState;
	}

	private MayAlias processAssertStatement(final MayAlias currentState, final AssertStatement st) {
		return currentState;
	}

	private void processAssumeStatement(final MayAlias currentState, final AssumeStatement st) {
		analyzeExpression(currentState,st.getFormula());
	}

	private void analyzeExpression(final MayAlias currentState, final Expression formula) {

	}

	private void processAssignmentStatement(final MayAlias ma, final AssignmentStatement st) {
		if (st.getRhs()[0] instanceof FunctionApplication) {
			final FunctionApplication fa = (FunctionApplication) st.getRhs()[0];
			if (fa.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_INT)) {
				final PointerBase p = extractPointerBase(mAsfac, fa.getArguments()[1]);
				mWriteAddresses.add(p);
				mAccessAddresses.add(p);
			} else if (fa.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_POINTER)) {
				final PointerBase p = extractPointerBase(mAsfac, fa.getArguments()[2]);
				mWriteAddresses.add(p);
				mAccessAddresses.add(p);
			}
		}
		if (isIntArray(st.getLhs())) {
			final ArrayStoreExpression aae = (ArrayStoreExpression) st.getRhs()[0];
			final Expression expr = aae.getIndices()[0];
			final PointerBase index = extractPointerBase(mAsfac, expr);
			mWriteAddresses.add(index);
			mAccessAddresses.add(index);
		}
		final Map<PointerBase, PointerBase> variableUpdate = new HashMap<>();
		final Map<PointerBase, PointerBase> pointerArrayUpdate = new HashMap<>();
		final LeftHandSide[] lhs = st.getLhs();
		for (int i = 0; i < lhs.length; i++) {
			if (lhs[i] instanceof VariableLHS) {
				final VariableLHS vlhs = (VariableLHS) lhs[i];
				if (isBaseArray(vlhs.getIdentifier())) {
					final Pair<PointerBase, PointerBase> pair = extractPointerBaseUpdate(st.getRhs()[i]);
					pointerArrayUpdate.put(pair.getFirst(), pair.getSecond());
					if (!isNullPointer(pair.getSecond())) {
						throw new AssertionError("we have to do something");
					}
				} else if (isPointer(vlhs.getIdentifier())) {
					mAsfac.getPointerBase(vlhs.getIdentifier(), vlhs.getDeclarationInformation());
					final PointerBase pbLhs = mAsfac.getPointerBase(vlhs.getIdentifier(),
							vlhs.getDeclarationInformation());
					final PointerBase pbRhs = extractPointerBase(mAsfac, st.getRhs()[i]);
					variableUpdate.put(pbLhs, pbRhs);
				}
			} else {
				throw new AssertionError("LHS is " + lhs[i].getClass());
			}
		}
		if (variableUpdate.isEmpty() && pointerArrayUpdate.isEmpty()) {
			// nothing to do
		} else {
			for (final Entry<PointerBase, PointerBase> entry : variableUpdate.entrySet()) {
				if (isNullPointer(entry.getValue())) {
					ma.addPointerBase(mAsfac, entry.getKey());
				} else {
					ma.reportEquivalence(mAsfac, entry.getKey(), entry.getValue());
				}
			}
			for (final Entry<PointerBase, PointerBase> entry : pointerArrayUpdate.entrySet()) {
				if (isNullPointer(entry.getValue())) {
					ma.addPointerBase(mAsfac, entry.getKey());
				} else {
					final MemorySegment ms = mAsfac.getMemorySegment(entry.getKey());
					ma.reportEquivalence(mAsfac, ms, entry.getValue());
					mWriteAddresses.add(entry.getKey());
					mAccessAddresses.add(entry.getKey());
				}
			}
		}

	}

	private boolean isIntArray(final LeftHandSide[] lhss) {
		if (lhss.length != 1) {
			return false;
		}
		final LeftHandSide lhs = lhss[0];
		if (!(lhs instanceof VariableLHS)) {
			return false;
		}
		final VariableLHS vlhs = (VariableLHS) lhs;
		return vlhs.getIdentifier().equals(MemorySliceUtils.MEMORY_INT);
	}



	private Pair<PointerBase, PointerBase> extractPointerBaseUpdate(final Expression expression) {
		if (expression instanceof FunctionApplication) {
			final FunctionApplication fa = (FunctionApplication) expression;
			if (fa.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_POINTER)) {
				assert fa.getArguments().length == 3;
				assert isBaseArray(((IdentifierExpression) fa.getArguments()[0]).getIdentifier());
				final PointerBase index = extractPointerBase(mAsfac, fa.getArguments()[2]);
				final PointerBase value = mAsfac.getPointerBase(BigInteger.ZERO);
				return new Pair<>(index, value);
			}
		}
		if (!(expression instanceof ArrayStoreExpression)) {
			throw new AssertionError("No array!");
		} else {
			final ArrayStoreExpression ase = (ArrayStoreExpression) expression;
			final Expression arr = ase.getArray();
			if (!(arr instanceof IdentifierExpression)) {
				throw new AssertionError("Not pointerBase array!");
			}
			final IdentifierExpression ie = (IdentifierExpression) arr;
			if (!isBaseArray(ie.getIdentifier())) {
				throw new AssertionError("Not pointerBase array!");
			}
			if (ase.getIndices().length != 2) {
				throw new AssertionError("Not pointerBase array!");
			}
			final Expression indexExpr = ase.getIndices()[0];
			final PointerBase index = extractPointerBase(mAsfac, indexExpr);
			final Expression valueExpr = ase.getValue();
			final PointerBase value = extractPointerBase(mAsfac, valueExpr);
			return new Pair<>(index, value);
		}
	}

	public static PointerBase extractPointerBase(final AddressStoreFactory mAsfac, final Expression expression) {
		if (expression instanceof IntegerLiteral) {
			final BigInteger value = new BigInteger(((IntegerLiteral) expression).getValue());
			return mAsfac.getPointerBase(value);
		} else if (expression instanceof BitvecLiteral) {
			final BigInteger value = new BigInteger(((BitvecLiteral) expression).getValue());
			return mAsfac.getPointerBase(value);
		} else if (expression instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) expression;
			return mAsfac.getPointerBase(ie.getIdentifier(), ie.getDeclarationInformation());
		} else {
			throw new AssertionError("unknown PointerBase " + expression);
		}
	}

	private void processCallStatement(final MayAlias ma, final CallStatement st) {
		if (st.getMethodName().equals(MemorySliceUtils.ALLOC_INIT)) {
			assert st.getArguments().length == 2;
			final Expression tmp = st.getArguments()[1];
			final PointerBase pb = extractPointerBase(mAsfac, tmp);
			ma.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals(MemorySliceUtils.ALLOC_ON_HEAP)
				|| st.getMethodName().equals(MemorySliceUtils.ALLOC_ON_STACK)) {
			assert st.getLhs().length == 2;
			final PointerBase pb = mAsfac.getPointerBase(st.getLhs()[0].getIdentifier(),
					st.getLhs()[0].getDeclarationInformation());
			ma.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals(MemorySliceUtils.WRITE_POINTER)
				|| (st.getMethodName().equals(MemorySliceUtils.WRITE_UNCHECKED_POINTER))) {
			assert st.getArguments().length == 5;
			final Expression baseOfValueExpr = st.getArguments()[0];
			final Expression baseOfIndexExpr = st.getArguments()[2];
			final PointerBase baseOfValue = extractPointerBase(mAsfac, baseOfValueExpr);
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, baseOfIndexExpr);
			if (isNullPointer(baseOfValue)) {
				// do nothing
				return;
			} else {
				final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
				ma.reportEquivalence(mAsfac, ms, baseOfValue);
				mWriteAddresses.add(baseOfIndex);
				mAccessAddresses.add(baseOfIndex);
			}
		} else if (st.getMethodName().equals(MemorySliceUtils.READ_POINTER)
				|| st.getMethodName().equals(MemorySliceUtils.READ_UNCHECKED_POINTER)) {
			assert st.getArguments().length == 3;
			assert st.getLhs().length == 2;
			final Expression baseOfIndexExpr = st.getArguments()[0];
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, baseOfIndexExpr);
			final PointerBase baseOfLhs = mAsfac.getPointerBase(st.getLhs()[0].getIdentifier(),
					st.getLhs()[0].getDeclarationInformation());
			final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
			ma.reportEquivalence(mAsfac, baseOfLhs, ms);
			mAccessAddresses.add(baseOfIndex);

		} else if (st.getMethodName().equals(MemorySliceUtils.WRITE_INIT_INT)
				|| st.getMethodName().equals(MemorySliceUtils.WRITE_INT)
				|| st.getMethodName().equals(MemorySliceUtils.WRITE_UNCHECKED_INT)) {
			final Expression pointerBaseExpr = st.getArguments()[1];
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, pointerBaseExpr);
			mWriteAddresses.add(baseOfIndex);
			mAccessAddresses.add(baseOfIndex);
		} else if (st.getMethodName().equals(MemorySliceUtils.WRITE_INIT_POINTER)) {
		} else if (st.getMethodName().equals(MemorySliceUtils.READ_INT)
				|| st.getMethodName().equals(MemorySliceUtils.READ_UNCHECKED_INT)) {
			final Expression pointerBaseExpr = st.getArguments()[0];
			final PointerBase baseOfIndex = extractPointerBase(mAsfac, pointerBaseExpr);
			mAccessAddresses.add(baseOfIndex);
		} else if (st.getMethodName().equals(MemorySliceUtils.ULTIMATE_DEALLOC)) {
		} else if (st.getMethodName().equals("memcmp")) {
		} else {
			throw new AssertionError("unsupported method " + st.getMethodName());
		}
	}

//	private void update(final MayAlias[] states, final ArrayDeque<Integer> worklist, final int targetI,
//			final MayAlias currentState) {
//		assert (currentState != null);
//		if (states[targetI] == null) {
//			states[targetI] = currentState;
//			worklist.add(targetI);
//		} else if (!states[targetI].equals(currentState)) {
//			states[targetI] = states[targetI].join(currentState);
//			worklist.add(targetI);
//		} else {
//			// no change, no need to add something to worklist
//		}
//
//	}

	private boolean isPointer(final String identifier) {
		return identifier.endsWith(".base");
	}

	private boolean isNullPointer(final PointerBase pbRhs) {
		return (pbRhs.toString().equals("0"));
	}

	private boolean isBaseArray(final String identifier) {
		return identifier.equals("#memory_$Pointer$.base");
	}


	private class ExpressionAnalyzer extends BoogieVisitor {

		@Override
		protected Expression processExpression(final Expression expr) {
			// TODO Auto-generated method stub
			return super.processExpression(expr);
		}

		@Override
		protected void visit(final BinaryExpression expr) {
			if (expr.getOperator() == BinaryExpression.Operator.COMPEQ) {
				final AddressStore left = tryToExtractAddressStore(expr.getLeft());
				final AddressStore right = tryToExtractAddressStore(expr.getRight());
			}
		}

		private AddressStore tryToExtractAddressStore(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression ie = (IdentifierExpression) expr;
				if (isPointer(ie.getIdentifier())) {
					return extractPointerBase(mAsfac, ie);
				}
			} else if (expr instanceof IntegerLiteral) {
				return extractPointerBase(mAsfac, expr);
			} else if (expr instanceof BitvecLiteral) {
				throw new AssertionError("TODO");
			} else if (expr instanceof ArrayAccessExpression) {
				throw new AssertionError("Array Access");
			}
			return null;
		}

		@Override
		protected void visit(final ArrayAccessExpression expr) {
			final Expression fst = expr.getIndices()[0];

		}




	}


}