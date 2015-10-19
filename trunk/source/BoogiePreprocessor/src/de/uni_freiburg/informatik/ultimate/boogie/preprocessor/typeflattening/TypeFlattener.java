package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PlaceholderBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructBoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
class TypeFlattener {

	private final Logger mLogger;
	private final Map<String, PlaceholderTypeDeclaration> mGenericTypeDeclarations;
	private final Map<BoogieType, Set<BoogieType>> mGenericType2InstantiatedTypes;
	private final Map<BoogieType, Set<PlaceholderVarList>> mGenericType2Vars;

	TypeFlattener(final Logger logger) {
		mLogger = logger;
		mGenericTypeDeclarations = new LinkedHashMap<>();
		mGenericType2InstantiatedTypes = new HashMap<BoogieType, Set<BoogieType>>();
		mGenericType2Vars = new HashMap<BoogieType, Set<PlaceholderVarList>>();
	}

	void run(final Unit unit) {
		final List<Declaration> newdecls = new ArrayList<>();

		final FirstRun first = new FirstRun();
		for (final Declaration decl : unit.getDeclarations()) {
			final Declaration newdecl = first.processDeclaration(decl);
			if (newdecl != null) {
				newdecls.add(newdecl);
			}
		}

		consolidateMaps();

		final SecondRun second = new SecondRun();
		for (int i = 0; i < newdecls.size(); ++i) {
			newdecls.set(i, second.processDeclaration(newdecls.get(i)));
		}

		unit.setDeclarations(newdecls.toArray(new Declaration[newdecls.size()]));
		return;
	}

	private void consolidateMaps() {
		for (final Entry<BoogieType, Set<PlaceholderVarList>> gtype2vars : mGenericType2Vars.entrySet()) {
			final Set<BoogieType> instantiatedTypes = mGenericType2InstantiatedTypes.get(gtype2vars.getKey());
			for (final PlaceholderVarList var : gtype2vars.getValue()) {
				for (final BoogieType instantiatedType : instantiatedTypes) {
					var.addType(instantiatedType);
				}
			}
		}
	}

	private boolean isGeneric(final VarList vl) {
		// either the vl has an already defined generic type, or it is of a
		// generic array type
		return isGeneric(vl.getType());
	}

	private boolean isGeneric(final TypeDeclaration typeDecl) {
		final String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length > 0) {
			return true;
		}

		final ASTType synonyms = typeDecl.getSynonym();
		if (synonyms == null) {
			return false;
		}
		return isGeneric(synonyms);
	}

	private boolean isGeneric(final ASTType type) {
		if (type instanceof ArrayType) {
			final ArrayType atype = ((ArrayType) type);
			if (atype.getTypeParams().length > 0) {
				return true;
			}
			return isGeneric(atype.getValueType()) || Arrays.stream(atype.getIndexTypes()).anyMatch(this::isGeneric);
		} else if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			return ntype.getTypeArgs().length > 0 || mGenericTypeDeclarations.containsKey(ntype.getName());
		} else if (type instanceof StructType) {
			throw new UnsupportedOperationException("Structs should have been resolved already");
		} else if (type instanceof PrimitiveType) {
			return false;
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + (type == null ? "null" : type.getClass().getSimpleName()));
		}
	}

	private String getTypeName(ASTType atype) {
		if (atype instanceof NamedType) {
			return ((NamedType) atype).getName();
		}
		return null;
	}

	private PlaceholderTypeDeclaration findGenericDeclaration(String typeName) {
		for (final Entry<String, PlaceholderTypeDeclaration> possibleParent : mGenericTypeDeclarations.entrySet()) {
			if (possibleParent.getKey().equals(typeName)) {
				return possibleParent.getValue();
			}
		}
		return null;
	}

	private ASTType flatten(final ASTType type) {
		if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			if (ntype.getTypeArgs().length == 0) {
				if (mGenericTypeDeclarations.containsKey(ntype.getName())) {
					// this is a synonym and it should not be flattened
					return null;
				}
				return ntype;
			}

			final Set<ASTType> types = new HashSet<ASTType>();
			for (final ASTType arg : ntype.getTypeArgs()) {
				final ASTType flattened = flatten(arg);
				if (flattened == null) {
					return null;
				} else {
					types.add(flattened);
				}
			}
			return new NamedType(type.getLocation(), ntype.getName() + getNewTypeName(types), new ASTType[0]);
		} else if (type instanceof PrimitiveType) {
			return type;
		}
		return null;
	}

	private String getNewTypeName(final Set<ASTType> types) {
		final StringBuilder sb = new StringBuilder();
		for (ASTType type : types) {
			if (type instanceof NamedType) {
				sb.append("$").append(((NamedType) type).getName());
			} else if (type instanceof PrimitiveType) {
				sb.append("$").append(((PrimitiveType) type).getName());
			} else {
				throw new UnsupportedOperationException();
			}
		}
		return sb.toString();
	}

	private Set<BoogieType> getInstantiatedTypes(final BoogieType genericType) {
		final BoogieType realGenericType = genericType.getUnderlyingType();
		return mGenericType2InstantiatedTypes.get(realGenericType);
	}

	private void markGenericType(final BoogieType genericType, final PlaceholderVarList vl) {
		final BoogieType realGenericType = genericType.getUnderlyingType();
		Set<BoogieType> set = mGenericType2InstantiatedTypes.get(realGenericType);
		if (set == null) {
			set = new HashSet<BoogieType>();
			mGenericType2InstantiatedTypes.put(realGenericType, set);
		}

		Set<PlaceholderVarList> varlists = mGenericType2Vars.get(realGenericType);
		if (varlists == null) {
			varlists = new HashSet<PlaceholderVarList>();
			mGenericType2Vars.put(realGenericType, varlists);
		}
		varlists.add(vl);
	}

	private StringBuilder mangleTypeName(StringBuilder sb, final BoogieType type) {
		if (type instanceof ArrayBoogieType) {
			final ArrayBoogieType atype = (ArrayBoogieType) type;
			sb.append("A");
			for (int i = 0; i < atype.getIndexCount(); ++i) {
				sb.append("$");
				mangleTypeName(sb, atype.getIndexType(i));
			}
			sb.append("$");
			return mangleTypeName(sb, atype.getValueType());
		} else if (type instanceof ConstructedBoogieType) {
			final ConstructedBoogieType ctype = ((ConstructedBoogieType) type);
			sb.append("C").append("$").append(ctype.getConstr().getName());
			for (int i = 0; i < ctype.getParameterCount(); ++i) {
				sb.append("$");
				mangleTypeName(sb, ctype.getParameter(i));
			}
			return sb;
		} else if (type instanceof PlaceholderBoogieType) {
			return sb.append("__");
		} else if (type instanceof PrimitiveBoogieType) {
			return sb.append("P$").append(type.toString());
		} else if (type instanceof StructBoogieType) {
			final StructBoogieType sbtype = (StructBoogieType) type;
			sb.append("S");
			for (int i = 0; i < sbtype.getFieldCount(); ++i) {
				sb.append("$");
				mangleTypeName(sb, sbtype.getFieldType(i));
			}
			return sb;
		} else {
			throw new UnsupportedOperationException(
					"Cannot mangle unknown BoogieType " + (type == null ? "null" : type.getClass().getSimpleName()));
		}
	}

	private final class FirstRun extends BoogieTransformer {

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				if (isGeneric(tdecl)) {
					mLogger.info(tdecl);
					// a declaration of a generic type will be deleted. If we
					// can, we instantiate it right here
					final PlaceholderTypeDeclaration rtr = new PlaceholderTypeDeclaration(tdecl);
					mGenericTypeDeclarations.put(rtr.getIdentifier(), rtr);
					return rtr;
				}
				return tdecl;
			} else if (decl instanceof Procedure) {
				Procedure proc = (Procedure) decl;
				if (proc.getTypeParams().length > 0) {
					throw new UnsupportedOperationException(
							"We cannot (yet) flatten generic procedures: " + BoogiePrettyPrinter.printSignature(proc));
				}
			} else if (decl instanceof FunctionDeclaration) {
				FunctionDeclaration func = (FunctionDeclaration) decl;
				if (func.getTypeParams().length > 0) {
					throw new UnsupportedOperationException(
							"We cannot (yet) flatten generic functions: " + BoogiePrettyPrinter.printSignature(func));
				}
			}
			return super.processDeclaration(decl);
		}

		@Override
		protected VarList processVarList(final VarList vl) {
			if (isGeneric(vl)) {
				mLogger.info(vl);
				final PlaceholderVarList rtr = new PlaceholderVarList(vl);
				BoogieType bt = (BoogieType) vl.getType().getBoogieType();
				markGenericType(bt, rtr);
				return rtr;
			}
			return super.processVarList(vl);
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof ArrayAccessExpression) {
				final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
				final BoogieType atype = (BoogieType) aaexpr.getArray().getType();
				final Set<BoogieType> set = getInstantiatedTypes(atype);

				if (set != null) {
					// it is a generic
					final ArrayBoogieType genericType = (ArrayBoogieType) atype;
					final Expression[] idxExpr = aaexpr.getIndices().clone();
					final BoogieType[] idxTypes = new BoogieType[idxExpr.length];
					for (int i = 0; i < idxExpr.length; ++i) {
						idxExpr[i] = processExpression(idxExpr[i]);
						idxTypes[i] = (BoogieType) idxExpr[i].getType();
					}
					final ArrayBoogieType newArrayType = genericType.instantiate(idxTypes,
							(BoogieType) aaexpr.getType());
					assert newArrayType.getUnderlyingType().equals(newArrayType);

					set.add(newArrayType);
					final Expression arrayExpr = processExpression(aaexpr.getArray());

					final Expression rtr = new ArrayAccessExpression(expr.getLocation(), newArrayType,
							new StructAccessExpression(expr.getLocation(), newArrayType, arrayExpr,
									getStructFieldName(newArrayType)),
							idxExpr);

					mLogger.info(
							"Replaced " + BoogiePrettyPrinter.print(expr) + " with " + BoogiePrettyPrinter.print(rtr));
					return rtr;
				}
				mLogger.info(BoogiePrettyPrinter.print(expr) + " is not generic");
			} else if (expr instanceof ArrayStoreExpression) {
				final ArrayStoreExpression asexpr = (ArrayStoreExpression) expr;
				final BoogieType atype = (BoogieType) asexpr.getArray().getType();
				final Set<BoogieType> set = getInstantiatedTypes(atype);

				if (set != null) {
					final ArrayBoogieType btype = (ArrayBoogieType) atype;
					final Expression[] idxExpr = asexpr.getIndices().clone();
					final BoogieType[] idxTypes = new BoogieType[idxExpr.length];
					for (int i = 0; i < idxExpr.length; ++i) {
						idxTypes[i] = (BoogieType) idxExpr[i].getType();
					}
					final ArrayBoogieType newArrayType = btype.instantiate(idxTypes,
							(BoogieType) asexpr.getValue().getType());
					assert newArrayType.getUnderlyingType().equals(newArrayType);
					set.add(newArrayType);

					final Expression arrayFromStructExpression = new StructAccessExpression(expr.getLocation(),
							newArrayType, asexpr.getArray(), getStructFieldName(newArrayType));

					final Expression newArrayStoreExpr = new ArrayStoreExpression(expr.getLocation(), newArrayType,
							arrayFromStructExpression, asexpr.getIndices(), asexpr.getValue());

					// we have to fill in the actual struct type in a later run
					final Expression rtr = new StructConstructor(expr.getLocation(), null,
							new String[] { getStructFieldName(newArrayType) }, new Expression[] { newArrayStoreExpr });
					mLogger.info(
							"Replaced " + BoogiePrettyPrinter.print(expr) + " with " + BoogiePrettyPrinter.print(rtr));
					return rtr;
				}
				mLogger.info(BoogiePrettyPrinter.print(expr) + " is not generic");
			} else if (expr instanceof QuantifierExpression) {
				final QuantifierExpression qexpr = (QuantifierExpression) expr;
				if (qexpr.getTypeParams().length > 0) {
					throw new UnsupportedOperationException("We do not support generic quantifier expressions (yet): "
							+ BoogiePrettyPrinter.print(expr));
				}
			}
			return super.processExpression(expr);
		}

		private String getStructFieldName(ArrayBoogieType newArrayType) {
			final String rtr = mangleTypeName(new StringBuilder(), newArrayType).toString();
			return rtr;
		}
	}

	private final class SecondRun extends BoogieTransformer {
		@Override
		protected Declaration processDeclaration(Declaration decl) {
			return super.processDeclaration(decl);
		}
	}

	private final class PlaceholderTypeDeclaration extends TypeDeclaration {
		private static final long serialVersionUID = 602282055128508050L;
		private Set<ASTType> mTypes;
		private PlaceholderTypeDeclaration mParent;

		public PlaceholderTypeDeclaration(TypeDeclaration tdecl) {
			super(tdecl.getLocation(), tdecl.getAttributes(), tdecl.isFinite(), tdecl.getIdentifier(),
					tdecl.getTypeParams(), tdecl.getSynonym());
			mTypes = new HashSet<>();
			mParent = findParent();
		}

		private void addType(BoogieType type) {
			if (type == null) {
				return;
			}
			if (mParent != null) {
				mParent.addType(type);
			} else {
				mTypes.add(type.toASTType(getLocation()));
			}
		}

		private void addType(ASTType type) {
			if (type == null) {
				return;
			}
			if (mParent != null) {
				mParent.addType(type);
			} else {
				mTypes.add(type);
			}
		}

		private PlaceholderTypeDeclaration findParent() {
			if (getSynonym() == null) {
				return null;
			}

			final String typeName = getTypeName(getSynonym());
			if (typeName == null) {
				return null;
			}
			return findGenericDeclaration(typeName);
		}

		@Override
		public String toString() {
			return super.toString() + " (" + mTypes.toString() + ")";
		}
	}

	private final class PlaceholderVarList extends VarList {
		private static final long serialVersionUID = -4964753793362170227L;
		private PlaceholderTypeDeclaration mParent;
		private Set<ASTType> mTypes;

		public PlaceholderVarList(VarList vl) {
			super(vl.getLocation(), vl.getIdentifiers(), vl.getType(), vl.getWhereClause());
			mParent = findParent();
			mTypes = new HashSet<ASTType>();
			addType(flatten(getType()));
		}

		private PlaceholderTypeDeclaration findParent() {
			BoogieType bt = (BoogieType) getType().getBoogieType();
			ASTType atype = bt.toASTType(getLocation());
			String typename = getTypeName(atype);
			if (typename == null) {
				// this might be a generic variable; we have to duplicate it
				// based on its access
				return null;
			}
			return findGenericDeclaration(typename);
		}

		private void addType(BoogieType type) {
			if (type == null) {
				return;
			}

			if (mParent != null) {
				mParent.addType(type);
			} else {
				mTypes.add(type.toASTType(getLocation()));
			}
		}

		private void addType(ASTType type) {
			if (type == null) {
				return;
			}

			if (mParent != null) {
				mParent.addType(type);
			} else {
				mTypes.add(type);
			}
		}
		
		@Override
		public String toString() {
			return super.toString() + " (" + mTypes.toString() + ")";
		}
	}
}