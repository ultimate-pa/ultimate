package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.memoryhandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.HeapDataArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class ConstructMemcpyOrMemmove {
	private final MemoryHandler mMemoryHandler;
	private final ProcedureManager mProcedureManager;
	private final TypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final ExpressionTranslation mExpressionTranslation;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final TypeSizes mTypeSizes;

	public ConstructMemcpyOrMemmove(final MemoryHandler memoryHandler, final ProcedureManager procedureHandler,
			final TypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ExpressionTranslation expressionTranslation, final AuxVarInfoBuilder auxVarInfoBuilder,
			final TypeSizes typeSizes) {
		mMemoryHandler = memoryHandler;
		mProcedureManager = procedureHandler;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mExpressionTranslation = expressionTranslation;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeSizes = typeSizes;
	}
	/**
	 * Construct specification and implementation for our Boogie representation of the memcpy and memmove functions
	 * defined in 7.24.2.1 of C11.
	 *
	 * void *memcpy(void * restrict s1, const void * restrict s2, size_t n);
	 *
	 * void *memmove( void* dest, const void* src, size_t count );
	 *
	 * @param main
	 * @param heapDataArrays
	 * @return
	 */
	public List<Declaration> declareMemcpyOrMemmove(final CHandler main,
			final Collection<HeapDataArray> heapDataArrays, final MemoryModelDeclarations memCopyOrMemMove,
			final IASTNode hook) {
		assert memCopyOrMemMove == MemoryModelDeclarations.C_Memcpy
				|| memCopyOrMemMove == MemoryModelDeclarations.C_Memmove;

		final List<Declaration> memCpyDecl = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final VarList inPDest =
				new VarList(ignoreLoc, new String[] { SFO.MEMCPY_DEST }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSrc =
				new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SRC }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSize = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SIZE },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));
		final VarList outP =
				new VarList(ignoreLoc, new String[] { SFO.RES }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList[] inParams = new VarList[] { inPDest, inPSrc, inPSize };
		final VarList[] outParams = new VarList[] { outP };

		{
			final Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], memCopyOrMemMove.getName(),
					new String[0], inParams, outParams, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, ignoreLoc, memCopyOrMemMove.getName(), memCpyProcDecl);
		}

		final List<Declaration> bodyDecl = new ArrayList<>();
		final List<Statement> stmt = new ArrayList<>();

		final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();


		{
			final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
			bodyDecl.add(loopCtrAux.getVarDec());


			final ExpressionResult loopBody =
					constructMemcpyOrMemmoveDataLoopAssignment(heapDataArrays, loopCtrAux, SFO.MEMCPY_DEST,
							SFO.MEMCPY_SRC, memCopyOrMemMove.getName(), hook);
			bodyDecl.addAll(loopBody.getDeclarations());

			final IdentifierExpression sizeIdExprBody =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
							SFO.MEMCPY_SIZE,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, memCopyOrMemMove.getName()));

			final Expression one = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);

			stmt.addAll(mMemoryHandler.constructCountingLoop(
					mMemoryHandler.constructBoundExitCondition(sizeIdExprBody, loopCtrAux),
					loopCtrAux, one, loopBody.getStatements(),
					memCopyOrMemMove.getName()));
		}

		{
			final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
			bodyDecl.add(loopCtrAux.getVarDec());


			final ExpressionResult loopBody =
					constructMemcpyOrMemmovePointerLoopAssignment(heapDataArrays, loopCtrAux, SFO.MEMCPY_DEST,
							SFO.MEMCPY_SRC, memCopyOrMemMove.getName(), hook);
			bodyDecl.addAll(loopBody.getDeclarations());

			final IdentifierExpression sizeIdExprBody =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
							SFO.MEMCPY_SIZE,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, memCopyOrMemMove.getName()));

			final Expression pointerSize =  mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
					mExpressionTranslation.getCTypeOfPointerComponents(),
					new BigInteger(Integer.toString(mTypeSizes.getSizeOfPointer())));

			stmt.addAll(mMemoryHandler.constructCountingLoop(
					mMemoryHandler.constructBoundExitCondition(sizeIdExprBody, loopCtrAux),
					loopCtrAux, pointerSize, loopBody.getStatements(),
					memCopyOrMemMove.getName()));
		}

		final Body procBody =
				mProcedureManager.constructBody(ignoreLoc, bodyDecl.toArray(new VariableDeclaration[bodyDecl.size()]),
						stmt.toArray(new Statement[stmt.size()]), memCopyOrMemMove.getName());

		// make the specifications
		final ArrayList<Specification> specs = new ArrayList<>();

		final IdentifierExpression sizeIdExprDecl = // new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE);
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						SFO.MEMCPY_SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memCopyOrMemMove.getName()));

		// add requires #valid[dest!base];
		specs.addAll(mMemoryHandler.constructPointerBaseValidityCheck(ignoreLoc, SFO.MEMCPY_DEST,
				memCopyOrMemMove.getName()));
		// add requires #valid[src!base];
		specs.addAll(mMemoryHandler.constructPointerBaseValidityCheck(ignoreLoc, SFO.MEMCPY_SRC,
				memCopyOrMemMove.getName()));

		// add requires (#size + #dest!offset <= #length[#dest!base] && 0 <= #dest!offset)
		specs.addAll(mMemoryHandler.constructPointerTargetFullyAllocatedCheck(ignoreLoc, sizeIdExprDecl,
				SFO.MEMCPY_DEST, memCopyOrMemMove.getName()));

		// add requires (#size + #src!offset <= #length[#src!base] && 0 <= #src!offset)
		specs.addAll(mMemoryHandler.constructPointerTargetFullyAllocatedCheck(ignoreLoc, sizeIdExprDecl,
				SFO.MEMCPY_SRC, memCopyOrMemMove.getName()));

		// free ensures #res == dest;
		final EnsuresSpecification returnValue =
				mProcedureManager.constructEnsuresSpecification(
						ignoreLoc, true, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ,
								ExpressionFactory.constructIdentifierExpression(ignoreLoc,
										mTypeHandler.getBoogiePointerType(), SFO.RES,
										new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM,
												memCopyOrMemMove.getName())),
								ExpressionFactory
								.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
										SFO.MEMCPY_DEST, new DeclarationInformation(
												StorageClass.PROC_FUNC_INPARAM, memCopyOrMemMove.getName()))),
						Collections.emptySet());
		specs.add(returnValue);

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], memCopyOrMemMove.getName(),
				new String[0], inParams, outParams, null, procBody);
		memCpyDecl.add(memCpyProc);

		mProcedureManager.endCustomProcedure(main, memCopyOrMemMove.getName());

		return memCpyDecl;
	}


	/**
	 * Return the assignments that we do in the loop body of our memcpy or memmove implementation.
	 *
	 *
	 * background: C11 7.24.2.1.2
	 * The memcpy function copies n characters from the object pointed to by s2 into the object pointed to by s1.
	 *
	 * @param heapDataArrays
	 * @param loopCtr
	 * @param destPtrName
	 * @param srcPtrName
	 * @param valueType determines which type the pointers have (thus in which steps we have to increment the access
	 *    source and destination)
	 * @return
	 */
			private ExpressionResult constructMemcpyOrMemmoveDataLoopAssignment(
			final Collection<HeapDataArray> heapDataArrays, final AuxVarInfo loopCtrAux, final String destPtrName,
			final String srcPtrName, final String surroundingProcedure, final IASTNode hook) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final CType charCType = new CPrimitive(CPrimitives.CHAR);
		final Expression srcId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), srcPtrName,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));
		final Expression destId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), destPtrName,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));


		final ExpressionResultBuilder loopBody = new ExpressionResultBuilder();
		{
			final Expression currentSrc = mMemoryHandler.doPointerArithmetic(IASTBinaryExpression.op_plus,
					ignoreLoc, srcId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);
			final Expression currentDest = mMemoryHandler.doPointerArithmetic(IASTBinaryExpression.op_plus,
					ignoreLoc, destId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);

			for (final CPrimitives cPrim : mMemoryHandler.getRequiredMemoryModelFeatures().getDataOnHeapRequired()) {
				final CType cPrimType = new CPrimitive(cPrim);
				final Expression srcAcc;
				{
					final ExpressionResult srcAccExpRes = mMemoryHandler.getReadCall(currentSrc, cPrimType, true, hook);
					srcAcc = srcAccExpRes.getLrValue().getValue();
					loopBody.addStatements(srcAccExpRes.getStatements());
					loopBody.addDeclarations(srcAccExpRes.getDeclarations());
					assert srcAccExpRes.getOverapprs().isEmpty();
				}

				{
					final List<Statement> writeCall = mMemoryHandler.getWriteCall(ignoreLoc,
							LRValueFactory.constructHeapLValue(mTypeHandler, currentDest, cPrimType, null),
							srcAcc,
							cPrimType,
							true,
							hook);
					loopBody.addStatements(writeCall);
				}
			}
		}

		return loopBody.build();
	}

	private ExpressionResult constructMemcpyOrMemmovePointerLoopAssignment(
			final Collection<HeapDataArray> heapDataArrays, final AuxVarInfo loopCtrAux, final String destPtrName,
			final String srcPtrName, final String surroundingProcedure, final IASTNode hook) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final CType charCType = new CPrimitive(CPrimitives.CHAR);
		final Expression srcId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), srcPtrName,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));
		final Expression destId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), destPtrName,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));


		final ExpressionResultBuilder loopBody = new ExpressionResultBuilder();
		{
			final Expression currentSrc = mMemoryHandler.doPointerArithmetic(IASTBinaryExpression.op_plus,
					ignoreLoc, srcId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);
			final Expression currentDest = mMemoryHandler.doPointerArithmetic(IASTBinaryExpression.op_plus,
					ignoreLoc, destId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);

			if (mMemoryHandler.getRequiredMemoryModelFeatures().isPointerOnHeapRequired()) {
				final CType cPointer = new CPointer(new CPrimitive(CPrimitives.VOID));
				final Expression srcAcc;
				{
					final ExpressionResult srcAccExpRes = mMemoryHandler.getReadCall(currentSrc, cPointer, true,
							hook);
					srcAcc = srcAccExpRes.getLrValue().getValue();
					loopBody.addStatements(srcAccExpRes.getStatements());
					loopBody.addDeclarations(srcAccExpRes.getDeclarations());
					assert srcAccExpRes.getOverapprs().isEmpty();
				}

				{
					final List<Statement> writeCall = mMemoryHandler.getWriteCall(ignoreLoc,
							LRValueFactory.constructHeapLValue(mTypeHandler, currentDest, cPointer, null),
							srcAcc,
							cPointer,
							true,
							hook);
					loopBody.addStatements(writeCall);
				}
			}
		}

		return loopBody.build();
	}

}