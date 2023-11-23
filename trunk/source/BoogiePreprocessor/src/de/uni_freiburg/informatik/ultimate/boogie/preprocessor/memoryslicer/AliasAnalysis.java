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
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AliasAnalysis {

	private final AddressStoreFactory mAsfac;
	private final Set<PointerBase> mWriteAddresses;
	private final Set<PointerBase> mAccessAddresses;
	private final Map<String, Procedure> mProcedureToImplementation;
	private Procedure mCurrentProcedure;
	private final HashRelation<String, String> mReverseCallgraph = new HashRelation<>();
	private final HashRelation<String, PointerBase> mProcedureToWritePointers = new HashRelation<>();

	public AliasAnalysis(final AddressStoreFactory asfac, final Map<String, Procedure> map) {
		super();
		mAsfac = asfac;
		mWriteAddresses = new HashSet<>();
		mAccessAddresses = new HashSet<>();
		mProcedureToImplementation = map;
	}

	public Set<PointerBase> getWriteAddresses() {
		return mWriteAddresses;
	}

	public Set<PointerBase> getAccessAddresses() {
		return mAccessAddresses;
	}

	public HashRelation<String, String> getReverseCallgraph() {
		return mReverseCallgraph;
	}

	public HashRelation<String, PointerBase> getProcedureToWritePointers() {
		return mProcedureToWritePointers;
	}

	public MayAlias aliasAnalysis(final Unit unit) {
		final MayAlias ma = new MayAlias();
		for (final Declaration d : unit.getDeclarations()) {
			if (d instanceof Procedure) {
				final Procedure p = (Procedure) d;
				if (p.getBody() != null) {
					mCurrentProcedure = p;
					processBody(ma, p.getBody());
				}
			} else if (d instanceof Axiom) {
				final Axiom ax = (Axiom) d;
				analyzeExpression(ma, ax.getFormula());
			}
		}
		return ma;
	}

	private void processBody(final MayAlias ma, final Body body) {
		processStatementList(ma, body.getBlock());
	}

	private void processStatementList(final MayAlias ma, final Statement[] sts) {
		for (final Statement st : sts) {
			if (st instanceof GotoStatement) {
				// do nothing
			} else if (st instanceof Label) {
				// do nothing
			} else if (st instanceof CallStatement) {
				processCallStatement(ma, (CallStatement) st);
			} else if (st instanceof AssignmentStatement) {
				processAssignmentStatement(ma, (AssignmentStatement) st);
			} else if (st instanceof AssumeStatement) {
				processAssumeStatement(ma, (AssumeStatement) st);
			} else if (st instanceof AssertStatement) {
				processAssertStatement(ma, (AssertStatement) st);
			} else if (st instanceof HavocStatement) {
				// do nothing
			} else if (st instanceof ReturnStatement) {
				// do nothing
			} else if (st instanceof BreakStatement) {
				// do nothing
			} else if (st instanceof IfStatement) {
				analyzeExpression(ma, ((IfStatement) st).getCondition());
				processStatementList(ma, ((IfStatement) st).getThenPart());
				processStatementList(ma, ((IfStatement) st).getElsePart());
			} else if (st instanceof WhileStatement) {
				analyzeExpression(ma, ((WhileStatement) st).getCondition());
				processStatementList(ma, ((WhileStatement) st).getBody());
			} else if (st instanceof ForkStatement) {
				processForkStatement(ma, (ForkStatement) st);
			} else if (st instanceof JoinStatement) {
				processJoinStatement(ma, (JoinStatement) st);
			} else if (st instanceof AtomicStatement) {
				processStatementList(ma, ((AtomicStatement) st).getBody());
			} else {
				throw new MemorySliceException("Unsuppored " + st);
			}
		}
	}

	private void processJoinStatement(final MayAlias ma, final JoinStatement st) {
		for (final Expression arg : st.getThreadID()) {
			analyzeExpression(ma, arg);
		}
		if (st.getLhs().length != 0) {
			if (isPointerType(st.getLhs()[0].getType())) {
				final PointerBase returnOfJoin = extractPointerBaseFromVariableLhs(mAsfac, st.getLhs()[0]);
				ma.addPointerBase(mAsfac, returnOfJoin);
				// return value of join could potentially alias with the return values of all
				// procedures that have matching out params (one outParam which is a pointer)
				for (final Entry<String, Procedure> entry : mProcedureToImplementation.entrySet()) {
					final Procedure proc = entry.getValue();
					final VarList[] outParams = proc.getOutParams();
					if (outParams.length == 1) {
						final VarList outParam = outParams[0];
						if (isPointerType(outParam.getType().getBoogieType())) {
							final StorageClass sc;
							if (proc.getSpecification() == null) {
								sc = StorageClass.IMPLEMENTATION_OUTPARAM;
							} else {
								sc = StorageClass.PROC_FUNC_OUTPARAM;
							}
							final PointerBase outParamPointer = extractPointerBaseFromVarlist(mAsfac, outParam,
									new DeclarationInformation(sc, proc.getIdentifier()));
							ma.reportEquivalence(mAsfac, returnOfJoin, outParamPointer);
						}
					}
				}
			}
		}
	}

	private void processForkStatement(final MayAlias ma, final ForkStatement st) {
		for (final Expression arg : st.getArguments()) {
			analyzeExpression(ma, arg);
		}
	}

	private void processAssertStatement(final MayAlias ma, final AssertStatement st) {
		analyzeExpression(ma, st.getFormula());
	}

	private void processAssumeStatement(final MayAlias ma, final AssumeStatement st) {
		analyzeExpression(ma, st.getFormula());
	}

	private void analyzeExpression(final MayAlias ma, final Expression formula) {
		final ExpressionAnalyzer ea = new ExpressionAnalyzer(ma);
		ea.processExpression(formula);
	}

	private void processAssignmentStatement(final MayAlias ma, final AssignmentStatement st) {
		if (st.getRhs()[0] instanceof FunctionApplication) {
			final FunctionApplication fa = (FunctionApplication) st.getRhs()[0];
			if (fa.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_INT)
					|| fa.getIdentifier().equals(MemorySliceUtils.INIT_TO_ZERO_AT_POINTER_BASE_ADDRESS_POINTER)) {
				final PointerBase p = extractPointerBaseFromBase(mAsfac, fa.getArguments()[1]);
				ma.addPointerBase(mAsfac, p);
				mAccessAddresses.add(p);
				mWriteAddresses.add(p);
				mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), p);
				return;
			}
		}

		final LeftHandSide[] lhs = st.getLhs();
		for (int i = 0; i < lhs.length; i++) {
			if (lhs[i] instanceof VariableLHS) {
				final VariableLHS vlhs = (VariableLHS) lhs[i];
				if (isPointerType(vlhs.getType())) {
					final PointerBase pbLhs = extractPointerBaseFromVariableLhs(mAsfac, vlhs);
					final List<PointerBase> pbRhss = extractPointerBasesFromPointer(mAsfac, st.getRhs()[i]);
					for (final PointerBase pbRhs : pbRhss) {
						ma.reportEquivalence(mAsfac, pbLhs, pbRhs);
					}
				} else if (MemorySliceUtils.containsMemoryArrays(vlhs)) {
					throw new MemorySliceException("Unsupported: Memory array in LHS");
				}
			} else if (lhs[i] instanceof StructLHS) {
				final StructLHS slhs = (StructLHS) lhs[i];
				if (MemorySliceUtils.containsMemoryArrays(slhs)) {
					throw new MemorySliceException("Unsupported: Memory array in LHS");
				} else {
					if (isPointerType(slhs.getType())) {
						final List<PointerBase> values = extractPointerBasesFromPointer(mAsfac, st.getRhs()[i]);
						for (final PointerBase value : values) {
							ma.reportEquivalence(mAsfac, mAsfac.getStruct(), value);
						}
					}
				}
				// It looks like we only write pointers to structs but we never read pointers
				// from structs, hence nothing has to be done here
			} else if (lhs[i] instanceof ArrayLHS) {
				final ArrayLHS alhs = (ArrayLHS) lhs[i];
				final LeftHandSide array = alhs.getArray();
				if (MemorySliceUtils.isPointerArray(array)) {
					assert alhs.getIndices().length == 1;
					final List<PointerBase> indices = extractPointerBasesFromPointer(mAsfac, alhs.getIndices()[0]);
					final List<PointerBase> values = extractPointerBasesFromPointer(mAsfac, st.getRhs()[i]);
					for (final PointerBase index : indices) {
						ma.addPointerBase(mAsfac, index);
						mAccessAddresses.add(index);
						mWriteAddresses.add(index);
						mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), index);
						final MemorySegment ms = mAsfac.getMemorySegment(index);
						for (final PointerBase value : values) {
							ma.reportEquivalence(mAsfac, ms, value);
						}
					}
				} else if (MemorySliceUtils.isIntArray(array) || MemorySliceUtils.isRealArray(array)) {
					assert alhs.getIndices().length == 1;
					final List<PointerBase> indices = extractPointerBasesFromPointer(mAsfac, alhs.getIndices()[0]);
					for (final PointerBase index : indices) {
						ma.addPointerBase(mAsfac, index);
						mAccessAddresses.add(index);
						mWriteAddresses.add(index);
						mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), index);
					}
				} else {
					// probably a local array, we don't have to deal with that
					if (MemorySliceUtils.containsMemoryArrays(array)) {
						throw new MemorySliceException("Unsupported: Memory array in LHS");
					} else {
						if (isPointerType(alhs.getType())) {
							final List<PointerBase> values = extractPointerBasesFromPointer(mAsfac, st.getRhs()[i]);
							for (final PointerBase value : values) {
								ma.reportEquivalence(mAsfac, mAsfac.getArray(), value);
							}
						}
					}
				}
				if (MemorySliceUtils.containsMemoryArrays(st.getRhs()[i])) {
					throw new MemorySliceException("Unsupported: Memory array in RHS");
				}

			} else {
				throw new MemorySliceException("LHS is " + lhs[i].getClass());
			}
		}

	}

	public static int getIndexOfFirstMatch(final String[] array, final String elem) {
		for (int i = 0; i < array.length; i++) {
			if (elem.equals(array[i])) {
				return i;
			}
		}
		return -1;
	}

	private static Expression unzipStructAccess(final Expression expression) {
		if (expression instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expression;
			final String field = sae.getField();
			final Expression struct = sae.getStruct();
			if (struct instanceof StructConstructor) {
				final StructConstructor sc = (StructConstructor) struct;
				final int indexOfFistMatch = getIndexOfFirstMatch(sc.getFieldIdentifiers(), field);
				if (indexOfFistMatch != -1) {
					return unzipStructAccess(sc.getFieldValues()[indexOfFistMatch]);
				}
			}
		}
		return expression;
	}

	public static List<PointerBase> extractPointerBasesFromPointer(final AddressStoreFactory mAsfac,
			final Expression expression) {
		final Expression unzipped = unzipStructAccess(expression);
		assert (isPointerType(unzipped.getType()));
		if (unzipped instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) unzipped;
			final List<PointerBase> res1 = extractPointerBasesFromPointer(mAsfac, ite.getThenPart());
			final List<PointerBase> res2 = extractPointerBasesFromPointer(mAsfac, ite.getElsePart());
			final List<PointerBase> result = new ArrayList<>();
			result.addAll(res1);
			result.addAll(res2);
			return result;
		} else {
			return Collections.singletonList(extractPointerBaseFromPointer(mAsfac, unzipped));
		}
	}

	public static PointerBase extractPointerBaseFromPointer(final AddressStoreFactory mAsfac,
			final Expression expression) {
		final Expression unzipped = unzipStructAccess(expression);
		assert (isPointerType(unzipped.getType()));
		if (unzipped instanceof StructConstructor) {
			final StructConstructor sc = (StructConstructor) unzipped;
			if (!sc.getFieldIdentifiers()[0].equals("base")) {
				throw new MemorySliceException("Not pointer");
			}
			return extractPointerBaseFromBase(mAsfac, sc.getFieldValues()[0]);
		} else if (unzipped instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) unzipped;
			return mAsfac.getPointerBase(ie.getIdentifier(), ie.getDeclarationInformation());
		} else if (unzipped instanceof StructAccessExpression) {
			return mAsfac.getStruct();
		} else if (unzipped instanceof ArrayAccessExpression) {
			return mAsfac.getArray();
		} else {
			throw new MemorySliceException("unknown PointerBase " + unzipped);
		}
	}

	public static PointerBase extractPointerBaseFromBase(final AddressStoreFactory mAsfac,
			final Expression expression) {
		assert (expression.getType() instanceof BoogiePrimitiveType);
		if (expression instanceof IntegerLiteral) {
			final BigInteger value = new BigInteger(((IntegerLiteral) expression).getValue());
			return mAsfac.getPointerBase(value);
		} else if (expression instanceof BitvecLiteral) {
			final BigInteger value = new BigInteger(((BitvecLiteral) expression).getValue());
			return mAsfac.getPointerBase(value);
		} else if (expression instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expression;
			assert sae.getField().equals("base");
			return extractPointerBaseFromPointer(mAsfac, sae.getStruct());
		} else {
			throw new MemorySliceException("unknown PointerBase " + expression);
		}
	}

	public static PointerBase extractPointerBaseFromVarlist(final AddressStoreFactory mAsfac, final VarList varlist,
			final DeclarationInformation declInfo) {
		assert isPointerType(varlist.getType().getBoogieType());
		assert varlist.getIdentifiers().length == 1;
		return mAsfac.getPointerBase(varlist.getIdentifiers()[0], declInfo);
	}

	private static boolean isPointerType(final IBoogieType type) {
		// preprocess, note that getUnderlyingType of BoogieConstructedType can be
		// BoogieConstructedType
		final IBoogieType realType;
		if (type instanceof BoogieConstructedType) {
			realType = ((BoogieConstructedType) type).getUnderlyingType();
		} else {
			realType = type;
		}
		if (realType instanceof BoogieConstructedType) {
			final BoogieConstructedType bct = (BoogieConstructedType) type;
			return bct.getConstr().getName().equals("$Pointer$");
		}
		if (realType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) realType;
			if (bst.getFieldCount() == 2) {
				if (bst.getFieldIds()[0].equals("base") && bst.getFieldIds()[1].equals("offset")) {
					return true;
				}
			}
		}
		return false;
	}

	private void processCallStatement(final MayAlias ma, final CallStatement st) {
		mReverseCallgraph.addPair(st.getMethodName(), mCurrentProcedure.getIdentifier());
		if (st.getMethodName().equals(MemorySliceUtils.ALLOC_INIT)) {
			assert st.getArguments().length == 2;
			final Expression tmp = st.getArguments()[1];
			final PointerBase pb = extractPointerBaseFromBase(mAsfac, tmp);
			ma.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals(MemorySliceUtils.ALLOC_ON_HEAP)
				|| st.getMethodName().equals(MemorySliceUtils.ALLOC_ON_STACK)) {
			assert st.getLhs().length == 1;
			final PointerBase pb = extractPointerBaseFromVariableLhs(mAsfac, st.getLhs()[0]);
			ma.addPointerBase(mAsfac, pb);
		} else if (st.getMethodName().equals(MemorySliceUtils.WRITE_POINTER)
				|| (st.getMethodName().equals(MemorySliceUtils.WRITE_UNCHECKED_POINTER))
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_POINTER)) {
			assert st.getArguments().length == 3;
			final Expression baseOfValueExpr = st.getArguments()[0];
			final Expression baseOfIndexExpr = st.getArguments()[1];
			final List<PointerBase> basesOfValue = extractPointerBasesFromPointer(mAsfac, baseOfValueExpr);
			final List<PointerBase> basesOfIndex = extractPointerBasesFromPointer(mAsfac, baseOfIndexExpr);
			for (final PointerBase baseOfIndex : basesOfIndex) {
				mAccessAddresses.add(baseOfIndex);
				mWriteAddresses.add(baseOfIndex);
				mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), baseOfIndex);
				ma.addPointerBase(mAsfac, baseOfIndex);
				final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
				for (final PointerBase baseOfValue : basesOfValue) {
					ma.reportEquivalence(mAsfac, ms, baseOfValue);
				}
			}
		} else if (st.getMethodName().startsWith(MemorySliceUtils.READ_POINTER)
				|| st.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_POINTER)) {
			assert st.getArguments().length == 2;
			assert st.getLhs().length == 1;
			final Expression baseOfIndexExpr = st.getArguments()[0];
			final List<PointerBase> basesOfIndex = extractPointerBasesFromPointer(mAsfac, baseOfIndexExpr);
			final PointerBase baseOfLhs = extractPointerBaseFromVariableLhs(mAsfac, st.getLhs()[0]);
			for (final PointerBase baseOfIndex : basesOfIndex) {
				ma.addPointerBase(mAsfac, baseOfIndex);
				final MemorySegment ms = mAsfac.getMemorySegment(baseOfIndex);
				ma.reportEquivalence(mAsfac, baseOfLhs, ms);
				mAccessAddresses.add(baseOfIndex);
			}

		} else if (st.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_INT)
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_INT)
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_INT)
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_INIT_REAL)
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_REAL)
				|| st.getMethodName().startsWith(MemorySliceUtils.WRITE_UNCHECKED_REAL)) {
			final Expression pointerBaseExpr = st.getArguments()[1];
			final List<PointerBase> basesOfIndex = extractPointerBasesFromPointer(mAsfac, pointerBaseExpr);
			for (final PointerBase baseOfIndex : basesOfIndex) {
				ma.addPointerBase(mAsfac, baseOfIndex);
				mAccessAddresses.add(baseOfIndex);
				mWriteAddresses.add(baseOfIndex);
				mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), baseOfIndex);
			}
		} else if (st.getMethodName().startsWith(MemorySliceUtils.READ_INT)
				|| st.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_INT)
				|| st.getMethodName().startsWith(MemorySliceUtils.READ_REAL)
				|| st.getMethodName().startsWith(MemorySliceUtils.READ_UNCHECKED_REAL)) {
			final Expression pointerBaseExpr = st.getArguments()[0];
			final List<PointerBase> basesOfIndex = extractPointerBasesFromPointer(mAsfac, pointerBaseExpr);
			for (final PointerBase baseOfIndex : basesOfIndex) {
				ma.addPointerBase(mAsfac, baseOfIndex);
				mAccessAddresses.add(baseOfIndex);
			}
		} else if (st.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMSET)) {
			assert st.getArguments().length == 3;
			final Expression pointerBaseExpr = st.getArguments()[0];
			final PointerBase baseOfIndex = extractPointerBaseFromPointer(mAsfac, pointerBaseExpr);
			mAccessAddresses.add(baseOfIndex);
			mWriteAddresses.add(baseOfIndex);
			mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), baseOfIndex);
			assert st.getLhs().length == 1;
			final PointerBase returnedIndex = extractPointerBaseFromVariableLhs(mAsfac, st.getLhs()[0]);
			ma.reportEquivalence(mAsfac, baseOfIndex, returnedIndex);
		} else if (st.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMCPY)
				|| st.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_MEMMOVE)
				|| st.getMethodName().equals(MemorySliceUtils.ULTIMATE_C_STRCPY)) {
			// STRCPY has 2 arguments, others have three arguments
			assert st.getArguments().length == 3 || st.getArguments().length == 2;
			final PointerBase destIndex = extractPointerBaseFromPointer(mAsfac, st.getArguments()[0]);
			final PointerBase srcIndex = extractPointerBaseFromPointer(mAsfac, st.getArguments()[1]);
			mAccessAddresses.add(destIndex);
			mAccessAddresses.add(srcIndex);
			mWriteAddresses.add(destIndex);
			mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), destIndex);
			ma.reportEquivalence(mAsfac, destIndex, srcIndex);
			assert st.getLhs().length == 1;
			final PointerBase returnedIndex = extractPointerBaseFromVariableLhs(mAsfac, st.getLhs()[0]);
			ma.reportEquivalence(mAsfac, destIndex, returnedIndex);
		} else if (st.getMethodName().equals(MemorySliceUtils.ULTIMATE_DEALLOC)) {
			// do nothing
		} else if (mProcedureToImplementation.containsKey(st.getMethodName())) {
			// is procedure with implementation
			final Procedure p = mProcedureToImplementation.get(st.getMethodName());
			assert st.getArguments().length == p.getInParams().length;
			for (int i = 0; i < st.getArguments().length; i++) {
				final Expression arg = st.getArguments()[i];
				if (isPointerType(arg.getType())) {
					final StorageClass sc;
					if (p.getSpecification() == null) {
						sc = StorageClass.IMPLEMENTATION_INPARAM;
					} else {
						sc = StorageClass.PROC_FUNC_INPARAM;
					}
					final PointerBase inParamPointer = extractPointerBaseFromVarlist(mAsfac, p.getInParams()[i],
							new DeclarationInformation(sc, p.getIdentifier()));
					final List<PointerBase> argPointers = extractPointerBasesFromPointer(mAsfac, arg);
					for (final PointerBase argPointer : argPointers) {
						ma.reportEquivalence(mAsfac, argPointer, inParamPointer);
					}
				}
			}
			for (int i = 0; i < st.getLhs().length; i++) {
				final VariableLHS vlhs = st.getLhs()[i];
				if (isPointerType(vlhs.getType())) {
					final StorageClass sc;
					if (p.getSpecification() == null) {
						sc = StorageClass.IMPLEMENTATION_OUTPARAM;
					} else {
						sc = StorageClass.PROC_FUNC_OUTPARAM;
					}
					final PointerBase outParamPointer = extractPointerBaseFromVarlist(mAsfac, p.getOutParams()[i],
							new DeclarationInformation(sc, p.getIdentifier()));
					final PointerBase lhsPointer = extractPointerBaseFromVariableLhs(mAsfac, vlhs);
					ma.reportEquivalence(mAsfac, lhsPointer, outParamPointer);
					mAccessAddresses.add(lhsPointer);
					mWriteAddresses.add(lhsPointer);
					mProcedureToWritePointers.addPair(mCurrentProcedure.getIdentifier(), lhsPointer);
				}
			}
		} else {
			// do nothing
//			throw new MemorySliceException("unsupported method " + st.getMethodName());
		}
	}

	private PointerBase extractPointerBaseFromVariableLhs(final AddressStoreFactory asfac,
			final VariableLHS variableLHS) {
		assert (isPointerType(variableLHS.getType()));
		final PointerBase pb = mAsfac.getPointerBase(variableLHS.getIdentifier(),
				variableLHS.getDeclarationInformation());
		return pb;
	}

	public static boolean isNullPointer(final PointerBase pb) {
		if (pb instanceof PointerBaseIntLiteral) {
			final PointerBaseIntLiteral pbil = (PointerBaseIntLiteral) pb;
			return pbil.getValue().equals(BigInteger.ZERO);
		}
		return false;
	}

	private class ExpressionAnalyzer extends BoogieVisitor {

		private final MayAlias mMa;

		public ExpressionAnalyzer(final MayAlias ma) {
			mMa = ma;
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			return super.processExpression(expr);
		}

		@Override
		protected void visit(final BinaryExpression expr) {
			if (expr.getOperator() == BinaryExpression.Operator.COMPEQ) {
				if (isPointerType(expr.getLeft().getType())) {
					final List<PointerBase> left = extractPointerBasesFromPointer(mAsfac, expr.getLeft());
					final List<PointerBase> right = extractPointerBasesFromPointer(mAsfac, expr.getRight());
					for (final PointerBase l : left) {
						for (final PointerBase r : right) {
							mMa.reportEquivalence(mAsfac, l, r);
						}
					}
				}
			}
		}

	}

}