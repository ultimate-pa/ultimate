package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 * Represents the signature of a Boogie procedure in simpler terms, than the Procedure class. Used for tracking the
 * signatures of the dispatching procedures for function pointer calls. (ref. FunctionHandler)
 *
 * @author Alexander Nutz
 */
public class ProcedureSignature {
	private final ArrayList<ASTType> mInParams = new ArrayList<>();
	private final ASTType mReturnType;
	private final boolean mTakesVarArgs;
	private final String mStringRepresentation;

	public ProcedureSignature(final ITypeHandler typehandler, final CFunction cf) {
		for (final CDeclaration ip : cf.getParameterTypes()) {
			final ASTType type = typehandler.cType2AstType(LocationFactory.createIgnoreCLocation(), ip.getType());
			mInParams.add(type);
		}
		if (cf.getResultType() instanceof CPrimitive
				&& ((CPrimitive) cf.getResultType()).getType() == CPrimitives.VOID) {
			mReturnType = null;
		} else {
			mReturnType = typehandler.cType2AstType(LocationFactory.createIgnoreCLocation(), cf.getResultType());
		}
		mTakesVarArgs = cf.takesVarArgs();
		mStringRepresentation = buildStringRepresentation();
	}

	public ASTType getReturnType() {
		return mReturnType;
	}

	@Override
	public String toString() {
		return mStringRepresentation;
	}

	private String buildStringRepresentation() {
		final StringBuilder sb = new StringBuilder();
		sb.append("##fun~");
		String times = "";
		for (int i = 0; i < mInParams.size(); i++) {
			sb.append(times);
			final ASTType inParam = mInParams.get(i);
			flattenASTTypeName(inParam, sb);
			times = "~X~";
		}
		if (mTakesVarArgs) {
			sb.append("X~varArgs~");
		}
		sb.append("~TO~");
		sb.append(mReturnType != null ? BoogiePrettyPrinter.print(mReturnType) : "VOID");
		return sb.toString();
	}

	private StringBuilder flattenASTTypeName(final ASTType type, final StringBuilder sb) {
		if (type instanceof StructType) {
			final StructType structType = (StructType) type;
			final VarList[] fields = structType.getFields();
			for (final VarList field : fields) {
				final StringBuilder flatFieldType = flattenASTTypeName(field.getType(), new StringBuilder());
				for (int i = 0; i < field.getIdentifiers().length; ++i) {
					sb.append(flatFieldType);
				}
			}
		} else {
			sb.append(BoogiePrettyPrinter.print(type));
		}
		return sb;
	}

	@Override
	public boolean equals(final Object o) {
		return toString().equals(o.toString());
	}

	@Override
	public int hashCode() {
		return mStringRepresentation.hashCode();
	}
}
