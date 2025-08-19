package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/** This is a class that holds some declarations used during the memset declaration */
public class MemsetDeclarations {
	public static final String inParamPtr = "#ptr";
	public static final String inParamValue = "#value";
	public static final String inParamAmount = "#amount";
	public static final String outParamResult = "#res";

	private final ITypeHandler mTypeHandler;

	private final String mProcName;
	private final ASTType mInParamType;
	private final ILocation mLoc;

	MemsetDeclarations(final ILocation loc, final String procName, final ASTType inParamType,
			final ITypeHandler typeHandler) {
		mProcName = procName;
		mInParamType = inParamType;
		mLoc = loc;

		mTypeHandler = typeHandler;
	}

	/** Returns the actual name of the memset implementation */
	public String procName() {
		return mProcName;
	}

	/** Returns the list of input parameters */
	public VarList[] inParams(final CPrimitive sizeT) {
		final VarList inParamPtrVl =
				new VarList(mLoc, new String[] { inParamPtr }, mTypeHandler.constructPointerType(mLoc));
		final VarList inParamValueVl = new VarList(mLoc, new String[] { inParamValue }, mInParamType);
		final VarList inParamAmountVl =
				new VarList(mLoc, new String[] { inParamAmount }, mTypeHandler.cType2AstType(mLoc, sizeT));
		final VarList[] inParams = { inParamPtrVl, inParamValueVl, inParamAmountVl };
		return inParams;
	}

	/** Returns the list of output parameters */
	public VarList[] outParams() {
		final VarList outParamResultVl =
				new VarList(mLoc, new String[] { outParamResult }, mTypeHandler.constructPointerType(mLoc));
		final VarList[] outParams = { outParamResultVl };

		return outParams;
	}

	/** Returns the procedure declaration, used to register in the procedure manager */
	public Procedure procedureDeclaration(final CPrimitive sizeT) {
		return new Procedure(mLoc, new Attribute[0], mProcName, new String[0], inParams(sizeT), outParams(),
				new Specification[0], null);

	}

	/** Returns the specification that #res equals dest */
	public Specification resEqualsDestSpecification(final ProcedureManager procedureManager) {
		// free ensures #res == dest;
		final EnsuresSpecification returnValue = procedureManager.constructEnsuresSpecification(mLoc, true,
				ExpressionFactory.newBinaryExpression(mLoc, Operator.COMPEQ,
						ExpressionFactory.constructIdentifierExpression(mLoc, mTypeHandler.getBoogiePointerType(),
								outParamResult, new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, mProcName)),
						ExpressionFactory.constructIdentifierExpression(mLoc, mTypeHandler.getBoogiePointerType(),
								inParamPtr, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, mProcName))),
				Collections.emptySet());

		return returnValue;
	}
}
