package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PlaceholderBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.TypeConstructor;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
class TypeFlattener {

	private final Logger mLogger;
	private final Map<BoogieType, Set<BoogieType>> mGenericType2InstantiatedTypes;
	private final Map<StructConstructor, BoogieType> mStructConsts2BoogieTypes;
	private final Scope<String, Set<BoogieType>> mScope;

	private final Set<String> mNewUninterpretedType;
	private final Map<ASTType, ASTType> mOld2NewAstTypes;
	private final Map<BoogieType, BoogieType> mOld2NewBoogieTypes;

	private final Map<String, TypeConstructor> mTypeCache;

	TypeFlattener(final Logger logger) {
		mLogger = logger;
		mGenericType2InstantiatedTypes = new HashMap<BoogieType, Set<BoogieType>>();
		mStructConsts2BoogieTypes = new HashMap<StructConstructor, BoogieType>();
		mScope = new Scope<String, Set<BoogieType>>();
		mNewUninterpretedType = new HashSet<>();
		mOld2NewBoogieTypes = new HashMap<>();
		mOld2NewAstTypes = new HashMap<>();
		mTypeCache = new HashMap<String, TypeConstructor>();
	}

	void run(final Unit unit) {

		final ExposedTransformer[] transformers = new ExposedTransformer[] { new InstantiateInterpretedTypes(),
				new DeclareNewInterpretedTypes(), new InstantiateUninterpretedTypes(), };

		List<Declaration> newdecls = new ArrayList<>();
		List<Declaration> olddecls = new ArrayList<>();
		newdecls.addAll(Arrays.asList(unit.getDeclarations()));

		for (final ExposedTransformer transformer : transformers) {
			olddecls = newdecls;
			newdecls = new ArrayList<Declaration>();

			mLogger.info("Run " + transformer.getClass().getSimpleName());
			for (final Declaration decl : olddecls) {
				final Declaration newdecl = transformer.processDeclaration(decl);
				if (newdecl != null) {
					newdecls.add(newdecl);
				}
			}
			transformer.finish(newdecls);

		}

		unit.setDeclarations(newdecls.toArray(new Declaration[newdecls.size()]));
		return;
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
			return ntype.getTypeArgs().length > 0;
		} else if (type instanceof StructType) {
			final StructType stype = (StructType) type;
			for (VarList field : stype.getFields()) {
				if (isGeneric(field.getType())) {
					return true;
				}
			}
			return false;
		} else if (type instanceof PrimitiveType) {
			return false;
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + (type == null ? "null" : type.getClass().getSimpleName()));
		}
	}

	private boolean isGeneric(BoogieType type) {
		assert type != null;
		type = type.getUnderlyingType();

		if (type instanceof ArrayBoogieType) {
			final ArrayBoogieType atype = ((ArrayBoogieType) type);
			if (atype.getNumPlaceholders() > 0) {
				return true;
			}
			if (isGeneric(atype.getValueType())) {
				return true;
			}
			for (int i = 0; i < atype.getIndexCount(); ++i) {
				if (isGeneric(atype.getIndexType(i))) {
					return true;
				}
			}
			return false;

		} else if (type instanceof ConstructedBoogieType) {
			return ((ConstructedBoogieType) type).getParameterCount() > 0;
		} else if (type instanceof PrimitiveBoogieType) {
			return false;
		} else if (type instanceof PlaceholderBoogieType) {
			return true;
		} else if (type instanceof StructBoogieType) {
			final StructBoogieType stype = ((StructBoogieType) type);
			for (BoogieType ftype : stype.getFieldTypes()) {
				if (isGeneric(ftype)) {
					return true;
				}
			}
			return false;
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + (type == null ? "null" : type.getClass().getSimpleName()));
		}
	}

	private ASTType flatten(final ASTType type) {
		if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			if (ntype.getTypeArgs().length == 0) {
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

			final String newname = ntype.getName() + getNewTypeName(types);
			TypeConstructor typeconst = getTypeConstructor(newname);
			final BoogieType btype = BoogieType.createConstructedType(typeconst);
			return new NamedType(type.getLocation(), btype, newname, new ASTType[0]);
		} else if (type instanceof PrimitiveType) {
			return type;
		}
		return null;
	}

	private TypeConstructor getTypeConstructor(String newname) {
		TypeConstructor rtr = mTypeCache.get(newname);
		if (rtr == null) {
			rtr = new TypeConstructor(newname, false, 0, new int[0]);
			mTypeCache.put(newname, rtr);
		}
		return rtr;
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
		Set<BoogieType> rtr = mGenericType2InstantiatedTypes.get(realGenericType);
		if (rtr == null) {
			rtr = new HashSet<BoogieType>();
			mGenericType2InstantiatedTypes.put(realGenericType, rtr);
		}
		return rtr;
	}

	private StringBuilder mangleTypeName(final StringBuilder sb, final BoogieType type) {
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

	private String prettyPrintTyped(IdentifierExpression iexpr) {
		return iexpr.getIdentifier() + " (" + iexpr.getType() + ")";
	}

	private ASTType getNewType(final ASTType oldtype) {
		// check if we already instantiated it
		ASTType newtype = mOld2NewAstTypes.get(oldtype);
		if (newtype != null) {
			return newtype;
		}

		newtype = flatten(oldtype);
		if (newtype == null) {
			// cannot flatten directly
			return null;
		}
		final String uninterpretedTypeName = BoogiePrettyPrinter.print(newtype);
		mOld2NewAstTypes.put(oldtype, newtype);

		final BoogieType oldboogietype = (BoogieType) oldtype.getBoogieType();
		final BoogieType newboogietype = BoogieType.createConstructedType(getTypeConstructor(uninterpretedTypeName));
		mOld2NewBoogieTypes.put(oldboogietype, newboogietype);

		mNewUninterpretedType.add(uninterpretedTypeName);
		return newtype;
	}

	private ASTType instantiateType(final ASTType oldtype) {
		assert oldtype != null;
		assert oldtype.getBoogieType() != null;

		final BoogieType btype = ((BoogieType) oldtype.getBoogieType()).getUnderlyingType();
		if (!isGeneric(btype)) {
			return null;
		}

		final ASTType newtype = getNewType(oldtype);
		if (newtype == null) {
			return null;
		}
		mLogger.info(
				"Replaced type " + BoogiePrettyPrinter.print(oldtype) + " with " + BoogiePrettyPrinter.print(newtype));
		return newtype;
	}

	private Set<BoogieType> addToDeclaration(String id, BoogieType type) {
		Set<BoogieType> set = mScope.lookupCurrentScope(id);
		if (set == null) {
			set = new HashSet<BoogieType>();
			mScope.declare(id, set);
		}
		set.add(type);
		return set;
	}

	private String getStructFieldName(final BoogieType newArrayType) {
		return mangleTypeName(new StringBuilder(), newArrayType).toString();
	}

	private String getStructFieldName(final ASTType type) {
		return getStructFieldName((BoogieType) type.getBoogieType());
	}

	private AssignmentStatement replaceArrayLHS(AssignmentStatement assign) {
		LeftHandSide[] lhs = assign.getLhs();
		Expression[] rhs = assign.getRhs();
		boolean changed = false;
		for (int i = 0; i < lhs.length; i++) {
			while (lhs[i] instanceof ArrayLHS) {
				LeftHandSide array = ((ArrayLHS) lhs[i]).getArray();
				Expression[] indices = ((ArrayLHS) lhs[i]).getIndices();
				Expression arrayExpr = (Expression) getLHSExpression(array);
				rhs[i] = new ArrayStoreExpression(lhs[i].getLocation(), array.getType(), arrayExpr, indices, rhs[i]);
				lhs[i] = array;
				changed = true;
			}
		}
		if (changed) {
			AssignmentStatement newAssign = new AssignmentStatement(assign.getLocation(), lhs, rhs);
			ModelUtils.mergeAnnotations(assign, newAssign);
			return newAssign;
		}
		return assign;
	}

	private Expression getLHSExpression(LeftHandSide lhs) {
		Expression expr;
		if (lhs instanceof ArrayLHS) {
			ArrayLHS arrlhs = (ArrayLHS) lhs;
			Expression array = getLHSExpression(arrlhs.getArray());
			expr = new ArrayAccessExpression(lhs.getLocation(), lhs.getType(), array, arrlhs.getIndices());
		} else {
			VariableLHS varlhs = (VariableLHS) lhs;
			expr = new IdentifierExpression(lhs.getLocation(), lhs.getType(), varlhs.getIdentifier(),
					varlhs.getDeclarationInformation());
		}
		return expr;
	}

	/**
	 * Necessary so I can call {@link #processDeclaration(Declaration)}.
	 * 
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static class ExposedTransformer extends BoogieTransformer {
		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			return super.processDeclaration(decl);
		}

		protected void finish(List<Declaration> decls) {

		}
	}

	private final class InstantiateInterpretedTypes extends ExposedTransformer {

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof Procedure) {
				final Procedure proc = (Procedure) decl;
				if (proc.getTypeParams().length > 0) {
					throw new UnsupportedOperationException(
							"We cannot (yet) flatten generic procedures: " + BoogiePrettyPrinter.printSignature(proc));
				}
				mScope.beginScope(decl);
				final Declaration rtr = super.processDeclaration(decl);
				mScope.endScope(decl, rtr);
				return rtr;
			} else if (decl instanceof FunctionDeclaration) {
				final FunctionDeclaration func = (FunctionDeclaration) decl;
				if (func.getTypeParams().length > 0) {
					throw new UnsupportedOperationException(
							"We cannot (yet) flatten generic functions: " + BoogiePrettyPrinter.printSignature(func));
				}
				mScope.beginScope(decl);
				final Declaration rtr = super.processDeclaration(decl);
				mScope.endScope(decl, rtr);
				return rtr;
			} else {
				return super.processDeclaration(decl);
			}
		}

		@Override
		protected VarList processVarList(VarList vl) {
			for (final String id : vl.getIdentifiers()) {
				addToDeclaration(id, (BoogieType) vl.getType().getBoogieType());
			}
			return super.processVarList(vl);
		}

		@Override
		protected Body processBody(final Body body) {
			mScope.beginScope(body);
			final Body rtr = super.processBody(body);
			mScope.endScope(body, rtr);
			return rtr;
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof ArrayAccessExpression) {
				final ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
				final BoogieType atype = (BoogieType) aaexpr.getArray().getType();
				if (isGeneric(atype)) {
					final Set<BoogieType> set = getInstantiatedTypes(atype);
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
					mLogger.info("Instantiated " + genericType + " with " + newArrayType);

					final Expression arrayExpr = processExpression(aaexpr.getArray());
					assert arrayExpr instanceof IdentifierExpression;

					// we have to set the struct type later as we currently not
					// know it
					final Expression rtr = new ArrayAccessExpression(expr.getLocation(), newArrayType,
							new StructAccessExpression(expr.getLocation(), null, arrayExpr,
									getStructFieldName(newArrayType)),
							idxExpr);
					ModelUtils.mergeAnnotations(expr, rtr);
					mLogger.info("Replaced ArrayAccessExpression " + BoogiePrettyPrinter.print(expr) + " with "
							+ BoogiePrettyPrinter.print(rtr));
					return rtr;
				}
				mLogger.info(BoogiePrettyPrinter.print(expr) + " is not generic");
				return super.processExpression(expr);
			} else if (expr instanceof ArrayStoreExpression) {
				final ArrayStoreExpression asexpr = (ArrayStoreExpression) expr;
				final BoogieType atype = (BoogieType) asexpr.getArray().getType();

				if (isGeneric(atype)) {
					final Set<BoogieType> set = getInstantiatedTypes(atype);
					final Expression[] newIdxExpr = new Expression[asexpr.getIndices().length];
					final BoogieType[] idxTypes = new BoogieType[asexpr.getIndices().length];
					for (int i = 0; i < newIdxExpr.length; ++i) {
						newIdxExpr[i] = processExpression(asexpr.getIndices()[i]);
						idxTypes[i] = (BoogieType) newIdxExpr[i].getType();
					}
					final ArrayBoogieType btype = (ArrayBoogieType) atype;
					final ArrayBoogieType newArrayType = btype.instantiate(idxTypes,
							(BoogieType) asexpr.getValue().getType());
					assert newArrayType.getUnderlyingType().equals(newArrayType);
					// remember the instantiation later
					mLogger.info("Instantiated " + btype + " with " + newArrayType);
					set.add(newArrayType);

					final Expression newArrayExpr = processExpression(asexpr.getArray());
					assert newArrayExpr instanceof IdentifierExpression;

					final Expression newValueExpr = processExpression(asexpr.getValue());
					final Expression arrayFromStructExpression = new StructAccessExpression(expr.getLocation(),
							newArrayType, newArrayExpr, getStructFieldName(newArrayType));

					final Expression newArrayStoreExpr = new ArrayStoreExpression(expr.getLocation(), newArrayType,
							arrayFromStructExpression, newIdxExpr, newValueExpr);

					// we have to fill in the actual struct type in a later run
					final StructConstructor rtr = new StructConstructor(expr.getLocation(), null,
							new String[] { getStructFieldName(newArrayType) }, new Expression[] { newArrayStoreExpr });
					mLogger.info("Replaced ArrayStoreExpression " + BoogiePrettyPrinter.print(expr) + " with "
							+ BoogiePrettyPrinter.print(rtr));
					mStructConsts2BoogieTypes.put(rtr, atype);
					ModelUtils.mergeAnnotations(expr, rtr);
					return rtr;
				}
				mLogger.info(BoogiePrettyPrinter.print(expr) + " is not generic");
				return super.processExpression(expr);
			} else if (expr instanceof QuantifierExpression) {
				final QuantifierExpression qexpr = (QuantifierExpression) expr;
				if (qexpr.getTypeParams().length > 0) {
					throw new UnsupportedOperationException("We do not support generic quantifier expressions (yet): "
							+ BoogiePrettyPrinter.print(expr));
				}
				mScope.beginScope(expr);
				final Expression rtr = super.processExpression(expr);
				mScope.endScope(expr, rtr);
				return rtr;
			} else if (expr instanceof FunctionApplication) {
				mScope.beginScope(expr);
				final Expression rtr = super.processExpression(expr);
				mScope.endScope(expr, rtr);
				return rtr;
			} else {
				return super.processExpression(expr);
			}
		}

		@Override
		protected Statement processStatement(Statement statement) {
			if (statement instanceof AssignmentStatement) {
				statement = replaceArrayLHS((AssignmentStatement) statement);
			}
			return super.processStatement(statement);
		}
	}

	private final class DeclareNewInterpretedTypes extends ExposedTransformer {

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				final ASTType interpretedType = tdecl.getSynonym();
				if (interpretedType != null && isGeneric(interpretedType)) {
					if (interpretedType instanceof ArrayType) {
						// declare new struct type
						BoogieType oldBoogieType = (BoogieType) interpretedType.getBoogieType();
						Set<BoogieType> set = mGenericType2InstantiatedTypes.get(oldBoogieType);

						final ILocation loc = tdecl.getLocation();
						final int size = set.size();
						final VarList[] fields = new VarList[size];
						final String[] fNames = new String[size];
						final BoogieType[] fTypes = new BoogieType[size];

						int i = 0;
						for (final BoogieType newBoogieType : set) {
							ASTType newType = newBoogieType.toASTType(decl.getLocation());
							fNames[i] = getStructFieldName(newType);
							fTypes[i] = newBoogieType;
							fields[i] = new VarList(loc, new String[] { fNames[i] }, newType);
							++i;
						}

						final StructBoogieType boogieType = BoogieType.createStructType(fNames, fTypes);

						final ASTType synonym = processType(new StructType(loc, boogieType, fields));
						final TypeDeclaration newdecl = new TypeDeclaration(loc, tdecl.getAttributes(),
								tdecl.isFinite(), tdecl.getIdentifier(), new String[0], synonym);
						ModelUtils.mergeAnnotations(decl, newdecl);
						mLogger.info("Replaced typedecl " + BoogiePrettyPrinter.print(tdecl) + " with "
								+ BoogiePrettyPrinter.print(newdecl));
						mOld2NewBoogieTypes.put((BoogieType) interpretedType.getBoogieType(), boogieType);
						return newdecl;
					}
				}
				mLogger.info("Ignoring " + decl);
				return super.processDeclaration(decl);
			} else if (decl instanceof FunctionDeclaration || decl instanceof Procedure) {
				mScope.beginScope(decl);
				final Declaration rtr = super.processDeclaration(decl);
				mScope.endScope(decl, rtr);
				return rtr;
			} else {
				return super.processDeclaration(decl);
			}
		}

		@Override
		protected VarList processVarList(VarList vl) {
			final ASTType interpretedType = vl.getType();
			if (interpretedType != null && isGeneric(interpretedType)) {
				if (interpretedType instanceof ArrayType) {
					// declare new struct type
					BoogieType oldBoogieType = (BoogieType) interpretedType.getBoogieType();
					Set<BoogieType> set = mGenericType2InstantiatedTypes.get(oldBoogieType);
					if (set == null) {
						return super.processVarList(vl);
					}

					final ILocation loc = vl.getLocation();
					final int size = set.size();
					final VarList[] fields = new VarList[size];
					final String[] fNames = new String[size];
					final BoogieType[] fTypes = new BoogieType[size];

					int i = 0;
					for (final BoogieType newBoogieType : set) {
						ASTType newType = newBoogieType.toASTType(loc);
						fNames[i] = getStructFieldName(newType);
						fTypes[i] = newBoogieType;
						fields[i] = new VarList(loc, new String[] { fNames[i] }, newType);
						++i;
					}

					final StructBoogieType boogieType = BoogieType.createStructType(fNames, fTypes);

					final ASTType newAstType = processType(new StructType(loc, boogieType, fields));
					final VarList newvl = new VarList(loc, vl.getIdentifiers(), newAstType, vl.getWhereClause());
					ModelUtils.mergeAnnotations(vl, newvl);
					mLogger.info("Replaced varlist " + BoogiePrettyPrinter.print(vl) + " with "
							+ BoogiePrettyPrinter.print(newvl));
					mOld2NewBoogieTypes.put((BoogieType) interpretedType.getBoogieType(), boogieType);
					return newvl;
				}
			}
			return super.processVarList(vl);
		}

		@Override
		protected ASTType processType(final ASTType oldtype) {
			final ASTType newtype = instantiateType(oldtype);
			if (newtype == null) {
				return super.processType(oldtype);
			}
			ModelUtils.mergeAnnotations(oldtype, newtype);
			return newtype;
		}

		@Override
		protected Body processBody(final Body body) {
			mScope.beginScope(body);
			final Body rtr = super.processBody(body);
			mScope.endScope(body, rtr);
			return rtr;
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof StructConstructor) {
				return createStructConstructor((StructConstructor) expr);
			} else if (expr instanceof StructAccessExpression) {
				// replace all the wrong array types with the now known struct
				// type
				final StructAccessExpression saexpr = (StructAccessExpression) expr;
				if (saexpr.getStruct() instanceof IdentifierExpression) {
					final IType oldType = saexpr.getStruct().getType();
					if (oldType instanceof ArrayBoogieType) {
						final BoogieType newType = mOld2NewBoogieTypes.get(oldType);
						saexpr.getStruct().setType(newType);
						mLogger.info("Finalized struct access " + BoogiePrettyPrinter.print(saexpr)
								+ " by changing type from " + oldType + " to " + newType);
					}
				}
				return super.processExpression(expr);
			} else if (expr instanceof FunctionApplication || expr instanceof QuantifierExpression) {
				mScope.beginScope(expr);
				final Expression rtr = super.processExpression(expr);
				mScope.endScope(expr, rtr);
				return rtr;
			} else {
				return super.processExpression(expr);
			}
		}

		private StructConstructor createStructConstructor(final StructConstructor sconst) {
			final BoogieType oldBoogieType = mStructConsts2BoogieTypes.get(sconst);
			if (oldBoogieType == null) {
				// was non-generic struct, just ignore it
				return sconst;
			}

			final StructBoogieType newBoogieType = (StructBoogieType) mOld2NewBoogieTypes.get(oldBoogieType);
			assert newBoogieType != null;

			final int fcount = newBoogieType.getFieldCount();
			final String[] fieldIdentifiers = new String[fcount];
			final Expression[] fieldValues = new Expression[fcount];

			// we created those constructors earlier and know that they have
			// exactly one field
			assert sconst.getFieldIdentifiers().length == 1;
			assert sconst.getFieldValues().length == 1;
			final String tmpField = sconst.getFieldIdentifiers()[0];
			final Expression tmpFieldValue = processExpression(sconst.getFieldValues()[0]);

			// we also know that this one fieldvalue is an ArrayStoreExpression
			// that
			// gets the array from a StructAccessExpression, which references
			// the struct we want to use for the identity here
			final Expression struct = ((StructAccessExpression) ((ArrayStoreExpression) tmpFieldValue).getArray())
					.getStruct();

			final ILocation loc = sconst.getLocation();
			for (int i = 0; i < fcount; ++i) {
				final String id = newBoogieType.getFieldIds()[i];
				final BoogieType type = newBoogieType.getFieldType(i);
				fieldIdentifiers[i] = id;
				if (id.equals(tmpField)) {
					fieldValues[i] = tmpFieldValue;
				} else {
					fieldValues[i] = new StructAccessExpression(loc, type, struct, id);
				}
			}
			final StructConstructor rtr = new StructConstructor(loc, newBoogieType, fieldIdentifiers, fieldValues);
			ModelUtils.mergeAnnotations(sconst, rtr);
			mLogger.info("Finalized struct constructor with " + BoogiePrettyPrinter.print(rtr));
			return rtr;
		}
	}

	private final class InstantiateUninterpretedTypes extends ExposedTransformer {

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				if (tdecl.getSynonym() == null && isGeneric(tdecl)) {
					mLogger.info("Deleted declaration " + BoogiePrettyPrinter.print(tdecl));
					return null;
				}
				return super.processDeclaration(decl);
			} else if (decl instanceof FunctionDeclaration || decl instanceof Procedure) {
				mScope.beginScope(decl);
				final Declaration rtr = super.processDeclaration(decl);
				mScope.endScope(decl, rtr);
				return rtr;
			} else {
				return super.processDeclaration(decl);
			}
		}

		@Override
		protected VarList processVarList(final VarList vl) {
			final ASTType oldtype = vl.getType();
			if (!isGeneric(oldtype)) {
				return super.processVarList(vl);
			}

			final ASTType newtype = getNewType(oldtype);
			if (newtype == null) {
				return super.processVarList(vl);
			}

			final VarList rtr = new VarList(vl.getLocation(), vl.getIdentifiers(), newtype, vl.getWhereClause());
			ModelUtils.mergeAnnotations(vl, rtr);
			mLogger.info(
					"Replaced varlist " + BoogiePrettyPrinter.print(vl) + " with " + BoogiePrettyPrinter.print(rtr));
			return rtr;
		}

		@Override
		protected Expression processExpression(final Expression expr) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression iexpr = (IdentifierExpression) expr;
				final BoogieType oldtype = (BoogieType) iexpr.getType();
				final BoogieType newtype = mOld2NewBoogieTypes.get(oldtype);
				if (newtype != null) {
					final IdentifierExpression rtr = new IdentifierExpression(expr.getLocation(), newtype,
							iexpr.getIdentifier(), iexpr.getDeclarationInformation());
					ModelUtils.mergeAnnotations(expr, rtr);
					mLogger.info("Replaced expr " + prettyPrintTyped(iexpr) + " with " + prettyPrintTyped(rtr));
					return rtr;
				}
				return super.processExpression(expr);
			} else if (expr instanceof FunctionApplication || expr instanceof QuantifierExpression) {
				mScope.beginScope(expr);
				final Expression rtr = super.processExpression(expr);
				mScope.endScope(expr, rtr);
				return rtr;
			} else {
				return super.processExpression(expr);
			}
		}

		@Override
		protected ASTType processType(final ASTType oldtype) {
			final ASTType newtype = instantiateType(oldtype);
			if (newtype == null) {
				return super.processType(oldtype);
			}
			ModelUtils.mergeAnnotations(oldtype, newtype);
			return newtype;
		}

		@Override
		protected Body processBody(final Body body) {
			mScope.beginScope(body);
			final Body rtr = super.processBody(body);
			mScope.endScope(body, rtr);
			return rtr;
		}

		@Override
		protected void finish(final List<Declaration> decls) {
			// just adding new uninterpreted types (from the instantiation of
			// uninterpreted types)
			for (final String name : mNewUninterpretedType) {
				decls.add(0, new TypeDeclaration(null, new Attribute[0], false, name, new String[0]));
			}
		}
	}
}