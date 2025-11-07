package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.memoryhandler;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.HeapDataArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryArea;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModel;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarationsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.RequiredMemoryModelFeatures;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 * Constructs the Boogie procedure used to model calls to the C standard function
 * <code>void *realloc(void *ptr, size_t size);</code>
 *
 * Roughly we model it like this:
 * <ol>
 * <li>if (ptr == null) return malloc(size)
 * <li>oldptr := ptr
 * <li>free(ptr)
 * <li>res := malloc(size)
 * <li>mem[res.base] := mem[oldptr.base]
 * <li>return res
 * </ol>
 *
 * (for the last step, we may need an extra Boogie function because mem is a multidimensional Boogie array (rather than
 * a nested Boogie array)
 *
 * Note that the sub-array copying works, because ptr must match a "pointer returned earlier by a memory management
 * function".
 *
 * See also: C11 7.22.3.5
 *
 * 2 The realloc function deallocates the old object pointed to by ptr and returns a pointer to a new object that has
 * the size specified by size. The contents of the new object shall be the same as that of the old object prior to
 * deallocation, up to the lesser of the new and old sizes. Any bytes in the new object beyond the size of the old
 * object have indeterminate values.
 *
 * 3 If ptr is a null pointer, the realloc function behaves like the malloc function for the specified size. Otherwise,
 * if ptr does not match a pointer earlier returned by a memory management function, or if the space has been
 * deallocated by a call to the free or realloc function, the behavior is undefined. If memory for the new object cannot
 * be allocated, the old object is not deallocated and its value is unchanged.
 *
 * Note: here "memory management functions" include aligned_alloc, calloc, malloc, and realloc (listed in 7.22.3-1), In
 * particular passing a pointer to stack memory (from alloca or the addressof operator) is undefined behaviour. (My
 * interpretation of the standard.)
 *
 * 4 The realloc function returns a pointer to the new object (which may have the same value as a pointer to the old
 * object), or a null pointer if the new object could not be allocated.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public final class ConstructRealloc {
	private final MemoryHandler mMemoryHandler;
	private final ProcedureManager mProcedureManager;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final ExpressionTranslation mExpressionTranslation;
	private final IMemoryPointer mMemoryPointer;
	private final MemoryModel mMemoryModel;
	private final RequiredMemoryModelFeatures mRequiredMemoryModelFeatures;
	private final MemoryModelDeclarationsHandler mMemoryModelDeclarationsHandler;

	public ConstructRealloc(final MemoryHandler memoryHandler, final ProcedureManager procedureHandler,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ExpressionTranslation expressionTranslation, final IMemoryPointer memoryPointer,
			final MemoryModel memoryModel, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler declarationsHandler) {
		mMemoryHandler = memoryHandler;
		mProcedureManager = procedureHandler;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mExpressionTranslation = expressionTranslation;
		mMemoryPointer = memoryPointer;
		mMemoryModel = memoryModel;
		mRequiredMemoryModelFeatures = requiredMemoryModelFeatures;
		mMemoryModelDeclarationsHandler = declarationsHandler;
	}

	/**
	 *
	 * See {@link ConstructRealloc}
	 *
	 * @param main
	 * @return
	 */
	public List<Declaration> declareRealloc(final CHandler main, final Collection<HeapDataArray> heapDataArrays) {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ICType voidPointerType = CPointer.voidPointer();
		final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();
		final String reallocProcName = SFO.C_REALLOC;

		final BoogieType pointerType = mTypeHandler.getBoogiePointerType();

		/* in parameters ptr and size, out parameter */

		final VarList inPPtr =
				new VarList(ignoreLoc, new String[] { SFO.REALLOC_PTR }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSize =
				new VarList(ignoreLoc, new String[] { SFO.REALLOC_SIZE }, mTypeHandler.cType2AstType(ignoreLoc, sizeT));
		final VarList outP =
				new VarList(ignoreLoc, new String[] { SFO.RES }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList[] inParams = { inPPtr, inPSize };
		final VarList[] outParams = { outP };

		final Procedure reallocProcDecl = new Procedure(ignoreLoc, new Attribute[0], reallocProcName, new String[0],
				inParams, outParams, new Specification[0], null);
		mProcedureManager.beginCustomProcedure(main, ignoreLoc, reallocProcName, reallocProcDecl);

		final VariableLHS resultLhsImpl = ExpressionFactory.constructVariableLHS(ignoreLoc, pointerType, SFO.RES,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, reallocProcName));

		final IdentifierExpression sizeIdExprImpl = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogieTypeForSizeT(), SFO.REALLOC_SIZE,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, reallocProcName));

		final IdentifierExpression ptrIdExprImpl =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, pointerType, SFO.REALLOC_PTR,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, reallocProcName));

		final IdentifierExpression resultExprImpl =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, pointerType, SFO.RES,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, reallocProcName));

		final List<Declaration> bodyDecl = new ArrayList<>();
		final List<Statement> bodyStmts = new ArrayList<>();

		// if (ptr == NULL) { return malloc(size) }
		final Expression condition =
				ExpressionFactory.newBinaryExpression(ignoreLoc, BinaryExpression.Operator.COMPEQ, ptrIdExprImpl,
						mMemoryPointer.constructNullPointer(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents()));
		final Statement mallocCallStm =
				mMemoryHandler.getUltimateMemAllocCall(sizeIdExprImpl, resultLhsImpl, ignoreLoc, MemoryArea.HEAP);
		final Statement returnStm = new ReturnStatement(ignoreLoc);

		final Statement ifStatement = StatementFactory.constructIfStatement(ignoreLoc, condition,
				new Statement[] { mallocCallStm, returnStm }, new Statement[0]);
		bodyStmts.add(ifStatement);
		// res := malloc(size)
		bodyStmts
				.add(mMemoryHandler.getUltimateMemAllocCall(sizeIdExprImpl, resultLhsImpl, ignoreLoc, MemoryArea.HEAP));

		bodyStmts.addAll(mMemoryModel.constructReallocBodyStatements(ignoreLoc, reallocProcName, heapDataArrays,
				pointerType, ptrIdExprImpl, resultLhsImpl, resultExprImpl, sizeIdExprImpl, mRequiredMemoryModelFeatures,
				mMemoryModelDeclarationsHandler));

		// free(ptr)
		bodyStmts.add(mMemoryHandler.getDeallocCall(new RValue(ptrIdExprImpl, voidPointerType), ignoreLoc));

		final Body procBody =
				mProcedureManager.constructBody(ignoreLoc, bodyDecl.toArray(new VariableDeclaration[bodyDecl.size()]),
						bodyStmts.toArray(new Statement[bodyStmts.size()]), reallocProcName);

		// specification:
		final List<Specification> specs = new ArrayList<>();

		/*
		 * realloc has undefined behaviour if ptr does not come from a malloc.
		 *
		 * Sufficient condition for this in our memory model: ptr.offset != 0
		 *
		 * In the future we will probably distinguish between different types of allocation through different int values
		 * in the #valid-array
		 */

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure reallocProc = new Procedure(ignoreLoc, new Attribute[0], reallocProcName, new String[0],
				inParams, outParams, null, procBody);

		mProcedureManager.endCustomProcedure(main, reallocProcName);

		return Collections.singletonList(reallocProc);
	}
}
