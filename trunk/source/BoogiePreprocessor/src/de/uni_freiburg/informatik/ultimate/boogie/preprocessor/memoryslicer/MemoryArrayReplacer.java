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

import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MemoryArrayReplacer extends BoogieTransformer {

	private final AddressStoreFactory mAsFac;
	private final UnionFind<AddressStore> mUf;
	private final Map<AddressStore, Integer> mRepToMemorySlice;
	private final int[] mSliceAccessCounter;
	private int mAccessCounter;
	private final int[] mSliceInitializationCounter;
	private int mInitializationCounter;
	private final int[] mSliceWriteCounter;
	private int mWriteCounter;
	private final HashRelation<String, Integer> mProcedureToModifiedMemorySlices;
	private String mCurrentProcedure;

	public MemoryArrayReplacer(final AddressStoreFactory asfac, final MayAlias ma,
			final Map<AddressStore, Integer> repToArray,
			final HashRelation<String, Integer> procedureToModifiedMemorySlices) {
		mAsFac = asfac;
		mUf = ma.getAddressStores();
		mRepToMemorySlice = repToArray;
		mProcedureToModifiedMemorySlices = procedureToModifiedMemorySlices;
		mSliceAccessCounter = new int[mRepToMemorySlice.size()];
		mAccessCounter = 0;
		mSliceInitializationCounter = new int[mRepToMemorySlice.size()];
		mInitializationCounter = 0;
		mSliceWriteCounter = new int[mRepToMemorySlice.size()];
		mWriteCounter = 0;
	}

	public String generateLogMessage() {
		if (mSliceAccessCounter.length == 0) {
			return "No memory access in input program.";
		}
		final int accessesToLargestEquivalenceClass = Arrays.stream(mSliceAccessCounter).max().getAsInt();
		final long percentage = Math.round((((double) accessesToLargestEquivalenceClass) / mAccessCounter) * 100.0);
		return String.format(
				"Split %s memory accesses to %s slices as follows %s. %s percent of accesses are in the largest equivalence class. "
						+ "The %s initializations are split as follows %s. The %s writes are split as follows %s.",
				mAccessCounter, mSliceAccessCounter.length, Arrays.toString(mSliceAccessCounter), percentage,
				mInitializationCounter, Arrays.toString(mSliceInitializationCounter), mWriteCounter,
				Arrays.toString(mSliceWriteCounter));
	}

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		if (decl instanceof Procedure) {
			mCurrentProcedure = ((Procedure) decl).getIdentifier();
		}
		return super.processDeclaration(decl);
	}

	@Override
	protected Specification processSpecification(final Specification spec) {
		if (spec instanceof ModifiesSpecification) {
			final ModifiesSpecification ms = (ModifiesSpecification) spec;
			final Set<Integer> modifiedSlices = mProcedureToModifiedMemorySlices.getImage(mCurrentProcedure);
			return MemorySlicer.reviseModifiesSpec(modifiedSlices, ms, MemorySliceUtils.MEMORY_POINTER,
					MemorySliceUtils.MEMORY_INT, MemorySliceUtils.MEMORY_REAL);
		} else {
			return super.processSpecification(spec);
		}
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		if (statement instanceof CallStatement) {
			final CallStatement cs = (CallStatement) statement;
			if (cs.getMethodName().startsWith(MemorySliceUtils.READ_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_REAL)) {
				assert cs.getArguments().length == 2;
				final Expression pointerBaseExpr = cs.getArguments()[0];
				final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerBaseExpr);
				final String suffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceNumber);
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						cs.getLhs(), cs.getMethodName() + suffix, cs.getArguments());
				ModelUtils.copyAnnotations(statement, result);
				mAccessCounter++;
				mSliceAccessCounter[memorySliceNumber]++;
				return result;
			} else if (cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_INT)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_REAL)
					|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_REAL)) {
				assert cs.getArguments().length == 3;
				final Expression pointerBaseExpr = cs.getArguments()[1];
				final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerBaseExpr);
				final String suffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceNumber);
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						cs.getLhs(), cs.getMethodName() + suffix, cs.getArguments());
				ModelUtils.copyAnnotations(statement, result);
				mAccessCounter++;
				mSliceAccessCounter[memorySliceNumber]++;
				if (cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_INT)
						|| cs.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_REAL)) {
					mInitializationCounter++;
					mSliceInitializationCounter[memorySliceNumber]++;
				} else {
					mWriteCounter++;
					mSliceWriteCounter[memorySliceNumber]++;
				}
				return result;
			} else if (cs.getMethodName().equals(MemorySliceUtils.READ_POINTER)
					|| cs.getMethodName().equals(MemorySliceUtils.READ_UNCHECKED_POINTER)) {
				assert cs.getArguments().length == 2;
				final Expression pointerBaseExpr = cs.getArguments()[0];
				final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerBaseExpr);
				final String suffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceNumber);
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						cs.getLhs(), cs.getMethodName() + suffix, cs.getArguments());
				ModelUtils.copyAnnotations(statement, result);
				mAccessCounter++;
				mSliceAccessCounter[memorySliceNumber]++;
				return result;
			} else if (cs.getMethodName().equals(MemorySliceUtils.WRITE_POINTER)
					|| (cs.getMethodName().equals(MemorySliceUtils.WRITE_INIT_POINTER))
					|| (cs.getMethodName().equals(MemorySliceUtils.WRITE_UNCHECKED_POINTER))) {
				assert cs.getArguments().length == 3;
				final Expression pointerBaseExpr = cs.getArguments()[1];
				final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerBaseExpr);
				final String suffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceNumber);
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						cs.getLhs(), cs.getMethodName() + suffix, cs.getArguments());
				ModelUtils.copyAnnotations(statement, result);
				mAccessCounter++;
				mSliceAccessCounter[memorySliceNumber]++;
				if (cs.getMethodName().equals(MemorySliceUtils.WRITE_INIT_POINTER)) {
					mInitializationCounter++;
					mSliceInitializationCounter[memorySliceNumber]++;
				} else {
					mWriteCounter++;
					mSliceWriteCounter[memorySliceNumber]++;
				}
				return result;
			} else if (cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMSET)
					|| cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMCPY)
					|| cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMMOVE)
					|| cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_STRCPY)
					|| cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_REALLOC)) {
				// have different arguments, but for all functions the first is a pointer
				final Expression pointerBaseExpr = cs.getArguments()[0];
				final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerBaseExpr);
				final String suffix = MemorySliceUtils.constructMemorySliceSuffix(memorySliceNumber);
				final CallStatement result = new CallStatement(cs.getLoc(), cs.getAttributes(), cs.isForall(),
						cs.getLhs(), cs.getMethodName() + suffix, cs.getArguments());
				ModelUtils.copyAnnotations(statement, result);
				mAccessCounter++;
				mSliceAccessCounter[memorySliceNumber]++;
				mWriteCounter++;
				mSliceWriteCounter[memorySliceNumber]++;
				return result;
			} else if (cs.getMethodName().equals(MemorySliceUtils.ALLOC_INIT)) {
				// do nothing
			} else if (cs.getMethodName().equals(MemorySliceUtils.ALLOC_ON_STACK)) {
				// do nothing
			} else if (cs.getMethodName().equals(MemorySliceUtils.ALLOC_ON_HEAP)) {
				// do nothing
			} else if (cs.getMethodName().equals(MemorySliceUtils.ULTIMATE_DEALLOC)) {
				// do nothing
			} else {
				// do nothing
//				statement.toString();
			}
		}
		if (statement instanceof AssignmentStatement) {
			final AssignmentStatement as = (AssignmentStatement) statement;
			final AssignmentStatement tmp1 = handleInitToZero(as);
			if (tmp1 != null) {
				return tmp1;
			}
			final AssignmentStatement tmp2 = handleArrayWrite(as);
			if (tmp2 != null) {
				return tmp2;
			}
			if (MemorySliceUtils.containsMemoryArrays(statement)) {
				throw new MemorySliceException("Statement contains memory arrays " + statement);
			}
		}
		return super.processStatement(statement);
	}

	private AssignmentStatement handleArrayWrite(final AssignmentStatement as) {
		if (as.getLhs().length != 1) {
			return null;
		}
		final LeftHandSide oldLhs = as.getLhs()[0];
		if (!(oldLhs instanceof ArrayLHS)) {
			return null;
		}
		final ArrayLHS arr = (ArrayLHS) oldLhs;
		if (MemorySliceUtils.isPointerArray(arr.getArray()) || MemorySliceUtils.isIntArray(arr.getArray())
				|| MemorySliceUtils.isRealArray(arr.getArray())) {
			if (arr.getIndices().length != 1) {
				return null;
			}
			final Expression pointerExpr = arr.getIndices()[0];
			final int memorySliceNumber = getMemorySliceNumberFromPointer(pointerExpr);
			mAccessCounter++;
			mSliceAccessCounter[memorySliceNumber]++;
			mWriteCounter++;
			mSliceWriteCounter[memorySliceNumber]++;
			final String suffix = getMemorySliceSuffixFromPointer(pointerExpr);

			final String oldMemArrayId = ((VariableLHS) arr.getArray()).getIdentifier();
			final String newMemArrayId = oldMemArrayId + suffix;

			final IdentifierReplacer ir = new IdentifierReplacer(Collections.singletonMap(oldMemArrayId, newMemArrayId),
					null, null);

			final LeftHandSide newLhs = ir.processLeftHandSide(oldLhs);
			// value is unchanged
			final Expression value = as.getRhs()[0];
			if (MemorySliceUtils.containsMemoryArrays(value)) {
				throw new MemorySliceException("Contains mem arrays " + value);
			}
			final AssignmentStatement result = new AssignmentStatement(as.getLocation(), new LeftHandSide[] { newLhs },
					new Expression[] { value });
			ModelUtils.copyAnnotations(as, result);
			return result;
		}
		return null;
	}

	private AssignmentStatement handleInitToZero(final AssignmentStatement as) {
		if (as.getLhs().length != 1) {
			return null;
		}
		final LeftHandSide oldLhs = as.getLhs()[0];
		if (!(oldLhs instanceof VariableLHS)) {
			return null;
		}
		if (!(as.getRhs()[0] instanceof FunctionApplication)) {
			return null;
		}
		final FunctionApplication fa0 = (FunctionApplication) as.getRhs()[0];
		final String oldMemoryArrayId;
		if (fa0.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_INT)) {
			oldMemoryArrayId = MemorySliceUtils.MEMORY_INT;
		} else if (fa0.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_POINTER)) {
			oldMemoryArrayId = MemorySliceUtils.MEMORY_POINTER;
		} else {
			return null;
		}
		final FunctionApplication oldFa = (FunctionApplication) as.getRhs()[0];
		final Expression pointerBaseExpr = oldFa.getArguments()[1];
		final int memorySliceNumber = getMemorySliceNumberFromBase(pointerBaseExpr);
		mAccessCounter++;
		mSliceAccessCounter[memorySliceNumber]++;
		mWriteCounter++;
		mSliceWriteCounter[memorySliceNumber]++;
		final String suffix = getMemorySliceSuffixFromBase(pointerBaseExpr);
		final String newMemoryArrayId = oldMemoryArrayId + suffix;
		final VariableLHS newVlhs = MemorySliceUtils.replaceLeftHandSide(oldLhs,
				Collections.singletonMap(oldMemoryArrayId, newMemoryArrayId), null, null);
		final IdentifierExpression newId = MemorySliceUtils.replaceIdentifierExpression(oldFa.getArguments()[0],
				Collections.singletonMap(oldMemoryArrayId, newMemoryArrayId), null, null);
		final Expression[] args = new Expression[] { newId, pointerBaseExpr };
		final FunctionApplication newFa = new FunctionApplication(oldFa.getLoc(), oldFa.getType(),
				oldFa.getIdentifier(), args);
		ModelUtils.copyAnnotations(oldFa, newFa);
		final AssignmentStatement result = new AssignmentStatement(as.getLocation(), new LeftHandSide[] { newVlhs },
				new Expression[] { newFa });
		ModelUtils.copyAnnotations(as, result);
		return result;
	}

	private int getMemorySliceNumberFromBase(final Expression pointerBaseExpr) {
		final PointerBase pointerBase = AliasAnalysis.extractPointerBaseFromBase(mAsFac, pointerBaseExpr);
		final AddressStore rep = mUf.find(pointerBase);
		Objects.requireNonNull(rep);
		final Integer number = mRepToMemorySlice.get(rep);
		Objects.requireNonNull(number);
		return number;
	}

	private int getMemorySliceNumberFromPointer(final Expression pointerBaseExpr) {
		final PointerBase pointerBase = AliasAnalysis.extractPointerBaseFromPointer(mAsFac, pointerBaseExpr);
		final AddressStore rep = mUf.find(pointerBase);
		Objects.requireNonNull(rep);
		final Integer number = mRepToMemorySlice.get(rep);
		Objects.requireNonNull(number);
		return number;
	}

	private String getMemorySliceSuffixFromBase(final Expression pointerBaseExpr) {
		final int number = getMemorySliceNumberFromBase(pointerBaseExpr);
		return MemorySliceUtils.constructMemorySliceSuffix(number);
	}

	private String getMemorySliceSuffixFromPointer(final Expression pointerBaseExpr) {
		final int number = getMemorySliceNumberFromPointer(pointerBaseExpr);
		return MemorySliceUtils.constructMemorySliceSuffix(number);
	}

//	@Override
//	protected Expression processExpression(final Expression expr) {
//		if (expr instanceof ArrayStoreExpression) {
//			throw new MemorySliceException("ArrayStoreExpression");
//		}
//		if (expr instanceof ArrayAccessExpression) {
//			if (!expr.toString().equals("ArrayAccessExpression[IdentifierExpression[#valid,GLOBAL],[IntegerLiteral[0]]]")) {
//				throw new MemorySliceException("ArrayStoreExpression");
//			}
////			final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
////			final Expression arr = processExpression(aaexpr.getArray());
////			final Expression[] indices = processExpressions(aaexpr.getIndices());
////			final Expression[] newIndices = processExpressions(indices);
////			if (arr instanceof IdentifierExpression) {
////				final IdentifierExpression ie = (IdentifierExpression) arr;
////				if (isHeap(ie.getIdentifier())) {
////					final Expression pointerBaseExpr = newIndices[0];
////					final PointerBase pointerBase = HeapSplitter.extractPointerBase(mAsFac, aaexpr);
////					final AddressStore rep = mUf.find(pointerBase);
////					final Expression newArray = null;
////					final ArrayAccessExpression result = new ArrayAccessExpression(aaexpr.getLocation(),
////							aaexpr.getType(), newArray, newIndices);
////					ModelUtils.copyAnnotations(expr, result);
////					return result;
////				}
////			}
//		}
//		return super.processExpression(expr);
//	}

}
