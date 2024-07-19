/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.standardfunctions;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTName;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.core.dom.ast.IBinding;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FindBindingReferences;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer.IPointerReadWrite;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Manages thread IDs for calls of pthread_create and pthread_join.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ThreadIdManager {
	/**
	 * Optimization that creates thread IDs with different types in certain situations where it is sound to do so. This
	 * allows to statically constrain which threads can be joined by a join statement, leading to faster analyses.
	 */
	private static final boolean UNAMBIGUOUS_THREAD_ID_OPTIMIZATION = true;

	/**
	 * Use the symbol table to determine the scope of a variable and only search for references within this scope.
	 */
	private static final boolean SYMBOL_TABLE_BASED_REFERENCE_SEARCH = true;

	private final Collection<IASTTranslationUnit> mTranslationUnits;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ExpressionResultTransformer mExpressionResultTransformer;
	private final ExpressionTranslation mExpressionTranslation;
	private final MemoryHandler mMemoryHandler;
	private final ITypeHandler mTypeHandler;
	private final TypeSizes mTypeSizes;
	private final FlatSymbolTable mSymbolTable;

	private final Map<IBinding, Integer> mUnambiguousThreadIds = new HashMap<>();

	public ThreadIdManager(final AuxVarInfoBuilder auxVarInfoBuilder,
			final ExpressionResultTransformer expressionResultTransformer,
			final ExpressionTranslation expressionTranslation, final MemoryHandler memoryHandler,
			final ITypeHandler typeHandler, final TypeSizes typeSizes,
			final Collection<IASTTranslationUnit> translationUnits, final FlatSymbolTable symbolTable) {
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mExpressionResultTransformer = expressionResultTransformer;
		mExpressionTranslation = expressionTranslation;
		mTranslationUnits = translationUnits;
		mMemoryHandler = memoryHandler;
		mTypeHandler = typeHandler;
		mTypeSizes = typeSizes;
		mSymbolTable = symbolTable;
	}

	/**
	 * Creates an expression denoting the thread ID for a newly forked thread.
	 *
	 * @param argument
	 *            The thread ID argument passed to a call of pthread_create.
	 * @param dispatcher
	 * @param loc
	 *            The location of the call
	 * @param hook
	 * @param erb
	 *            A result builder to which declarations, auxiliaries and statements necessary to compute the thread ID
	 *            are added.
	 * @return a Boogie expression to be used in a fork statement
	 */
	public Expression[] updateForkedThreadId(final IASTInitializerClause argument, final IDispatcher dispatcher,
			final ILocation loc, final IASTNode hook, final ExpressionResultBuilder erb) {
		mMemoryHandler.requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_FORK_COUNT);

		final Expression threadId = getOldForkCounterAsTemp(loc, erb);
		incrementForkCounter(loc, erb);
		final IPointerReadWrite rw =
				mExpressionResultTransformer.dispatchPointerWithOptimization(dispatcher, loc, argument);
		erb.addAllExceptLrValue(rw.getDispatchedResult(), rw.getWrite(threadId));

		if (UNAMBIGUOUS_THREAD_ID_OPTIMIZATION) {
			final Integer unambiguousId = getUnambiguousThreadIdCounter(argument);
			if (unambiguousId != null) {
				return createUnambiguousThreadId(unambiguousId, loc, threadId);
			}
		}

		return new Expression[] { threadId };
	}

	/**
	 * Creates an expression denoting the thread ID for a thread to be joined.
	 *
	 * @param argument
	 *            The thread ID argument passed to a call of pthread_join
	 * @param dispatcher
	 * @param loc
	 *            The location of the call
	 * @param erb
	 *            A result builder to which declarations, auxiliaries and statements necessary to compute the thread ID
	 *            are added.
	 * @return a Boogie expression to be used in a join statement
	 */
	public Expression[] getJoinedThreadId(final IASTInitializerClause argument, final IDispatcher dispatcher,
			final ILocation loc, final ExpressionResultBuilder erb) {
		final CPrimitive threadIdType = mMemoryHandler.getThreadIdType();
		final ExpressionResult tmp =
				mExpressionResultTransformer.transformDispatchDecaySwitchRexBoolToInt(dispatcher, loc, argument);
		final ExpressionResult argThreadId =
				mExpressionResultTransformer.performImplicitConversion(tmp, threadIdType, loc);
		erb.addAllExceptLrValue(argThreadId);
		final Expression threadId = argThreadId.getLrValue().getValue();

		if (UNAMBIGUOUS_THREAD_ID_OPTIMIZATION) {
			final Integer unambiguousId = getUnambiguousThreadIdCounter(argument);
			if (unambiguousId != null) {
				return createUnambiguousThreadId(unambiguousId, loc, threadId);
			}
		}

		return new Expression[] { threadId };
	}

	/**
	 * Stores the value of the fork counter in an auxiliary variable and returns a reference to this auxiliary.
	 */
	private Expression getOldForkCounterAsTemp(final ILocation loc, final ExpressionResultBuilder erb) {
		// create temporary variable for fork counter value
		final AuxVarInfo tmpThreadId =
				mAuxVarInfoBuilder.constructAuxVarInfo(loc, mMemoryHandler.getThreadIdType(), SFO.AUXVAR.PRE_MOD);
		erb.addAuxVarWithDeclaration(tmpThreadId);

		// assignment: temp variable gets fork counter value
		final IdentifierExpression forkCount = mMemoryHandler.getPthreadForkCount(loc);
		final AssignmentStatement counterStore = new AssignmentStatement(loc,
				new LeftHandSide[] { tmpThreadId.getLhs() }, new Expression[] { forkCount });
		erb.addStatement(counterStore);

		return tmpThreadId.getExp();
	}

	/**
	 * Increments the value of the global fork counter.
	 */
	private void incrementForkCounter(final ILocation loc, final ExpressionResultBuilder erb) {
		final IdentifierExpression forkCount = mMemoryHandler.getPthreadForkCount(loc);
		final CPrimitive threadIdType = mMemoryHandler.getThreadIdType();

		final var counterLhs = new VariableLHS(loc, forkCount.getType(), forkCount.getIdentifier(),
				forkCount.getDeclarationInformation());
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				forkCount, threadIdType,
				mTypeSizes.constructLiteralForIntegerType(loc, threadIdType, BigInteger.valueOf(1L)), threadIdType);
		final AssignmentStatement counterIncrement =
				new AssignmentStatement(loc, new VariableLHS[] { counterLhs }, new Expression[] { sum });
		erb.addStatement(counterIncrement);
	}

	private Integer getUnambiguousThreadIdCounter(final IASTInitializerClause argument) {
		final IASTName threadIdName = getDirectReference(argument);
		if (threadIdName == null) {
			return null;
		}

		final IBinding threadIdBinding = threadIdName.resolveBinding();
		if (threadIdBinding == null) {
			return null;
		}

		final Integer storedId = mUnambiguousThreadIds.get(threadIdBinding);
		if (storedId != null) {
			return storedId;
		}

		final Set<IASTName> references = findAllReferences(threadIdBinding, threadIdName);
		if (references != null && onlyForkJoinReferences(references)) {
			final int idCounter = mUnambiguousThreadIds.size() + 1;
			mUnambiguousThreadIds.put(threadIdBinding, idCounter);
			return idCounter;
		}
		return null;
	}

	private Set<IASTName> findAllReferences(final IBinding binding, final IASTNode hook) {
		final FindBindingReferences finder = new FindBindingReferences(binding);

		if (SYMBOL_TABLE_BASED_REFERENCE_SEARCH) {
			final SymbolTableValue entry = mSymbolTable.findCSymbol(hook, binding.getName());
			if (entry == null) {
				assert false : "Cannot find binding in symbol table";
				return null;
			}

			final IASTNode scopeCursor = mSymbolTable.tableFindCursor(hook, binding.getName(), entry);
			if (scopeCursor == null) {
				assert false : "Cannot find symbol table value in the same symbol table";
				return null;
			}

			scopeCursor.accept(finder);
		} else {
			for (final IASTTranslationUnit unit : mTranslationUnits) {
				unit.accept(finder);
			}
		}

		return finder.getReferences();
	}

	private static IASTName getDirectReference(final IASTInitializerClause expression) {
		if (expression instanceof IASTIdExpression) {
			return ((IASTIdExpression) expression).getName();
		}

		if (!(expression instanceof IASTUnaryExpression)) {
			return null;
		}
		final IASTUnaryExpression unary = (IASTUnaryExpression) expression;
		if (unary.getOperator() != IASTUnaryExpression.op_amper || !(unary.getOperand() instanceof IASTIdExpression)) {
			return null;
		}
		final IASTIdExpression idExpr = (IASTIdExpression) unary.getOperand();
		return idExpr.getName();
	}

	private static boolean onlyForkJoinReferences(final Set<IASTName> references) {
		return references.stream().allMatch(ref -> isPthreadCreateReference(ref) || isPthreadJoinReference(ref));
	}

	private static boolean isPthreadCreateReference(final IASTName name) {
		final IASTNode idExprNode = name.getParent();
		if (!(idExprNode instanceof IASTIdExpression)) {
			return false;
		}
		final IASTNode ampExprNode = idExprNode.getParent();
		if (!(ampExprNode instanceof IASTUnaryExpression)) {
			return false;
		}
		final IASTUnaryExpression unary = (IASTUnaryExpression) ampExprNode;
		if (unary.getOperator() != IASTUnaryExpression.op_amper) {
			return false;
		}
		return isFirstArgumentOfFunCall(unary, "pthread_create");
	}

	private static boolean isPthreadJoinReference(final IASTName name) {
		final IASTNode idExprNode = name.getParent();
		if (!(idExprNode instanceof IASTIdExpression)) {
			return false;
		}
		return isFirstArgumentOfFunCall(idExprNode, "pthread_join");
	}

	private static boolean isFirstArgumentOfFunCall(final IASTNode expr, final String function) {
		final IASTNode funCallNode = expr.getParent();
		if (!(funCallNode instanceof IASTFunctionCallExpression)) {
			return false;
		}
		final IASTFunctionCallExpression funCall = (IASTFunctionCallExpression) funCallNode;
		if (funCall.getArguments().length == 0 || funCall.getArguments()[0] != expr) {
			return false;
		}
		final IASTExpression funNameExprNode = funCall.getFunctionNameExpression();
		if (!(funNameExprNode instanceof IASTIdExpression)) {
			return false;
		}
		final IASTIdExpression funNameExpr = (IASTIdExpression) funNameExprNode;
		final String funName = funNameExpr.getName().toString();
		return function.equals(funName);
	}

	private Expression[] createUnambiguousThreadId(final int count, final ILocation loc, final Expression forkCounter) {
		final Expression[] ids = new Expression[count + 1];
		ids[0] = forkCounter;
		for (int i = 0; i < count; ++i) {
			ids[i + 1] = mExpressionTranslation.constructZero(loc, new CPrimitive(CPrimitives.INT));
		}
		return ids;
	}
}
