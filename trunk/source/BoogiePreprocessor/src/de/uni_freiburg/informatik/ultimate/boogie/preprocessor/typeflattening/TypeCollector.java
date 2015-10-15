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
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PlaceholderBoogieType;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

class TypeCollector extends BoogieTransformer {

	private final Map<String, Declaration> mNewGlobals;

	private final Map<TypeDeclaration, Set<ASTType>> mInstantiations;
	private final Map<VarList, ASTType> mVariablesToReplace;

	private final Stack<Expression> mExpressionStack;

	private final Logger mLogger;

	TypeCollector(Logger logger) {
		mVariablesToReplace = new HashMap<VarList, ASTType>();
		mExpressionStack = new Stack<>();
		mInstantiations = new HashMap<TypeDeclaration, Set<ASTType>>();
		mNewGlobals = new LinkedHashMap<String, Declaration>();
		mLogger = logger;
	}

	void run(Unit unit) {
		final List<Declaration> newdecls = new ArrayList<>();

		// run 1: collect all types that need to be flattened
		for (final Declaration decl : unit.getDeclarations()) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration newdecl = processTypeDeclaration((TypeDeclaration) decl);
				if (newdecl != null) {
					mNewGlobals.put(newdecl.getIdentifier(), newdecl);
				}
			}
		}

		// run 2: flatten all types
		for (final Declaration decl : unit.getDeclarations()) {
			if (decl instanceof TypeDeclaration) {
				continue;
			}
			final Declaration newdecl = processDeclaration(decl);
			if (newdecl != null) {
				newdecls.add(newdecl);
			}
		}

		// run 3:
		// duplicate modifies, generic procedures, etc. with the used
		// types, replace all remaining (now undefined) variables with the

		// add all new declarations
		newdecls.addAll(0, mNewGlobals.values());

		unit.setDeclarations(newdecls.toArray(new Declaration[newdecls.size()]));
	}

	protected TypeDeclaration processTypeDeclaration(TypeDeclaration decl) {
		final TypeDeclaration tdecl = (TypeDeclaration) decl;
		if (isGeneric(tdecl)) {
			getInstantiations(tdecl);
			mLogger.info("Deleting " + BoogiePrettyPrinter.print(tdecl));
			// deletes this declaration
			return null;
		}
		return decl;
	}

	private Set<ASTType> getInstantiations(final TypeDeclaration tdecl) {
		Set<ASTType> rtr = mInstantiations.get(tdecl);
		if (rtr == null) {
			rtr = new HashSet<ASTType>();
			mInstantiations.put(tdecl, rtr);
		}
		return rtr;
	}

	private Set<ASTType> addInstantiation(final TypeDeclaration tdecl, final ASTType newType) {
		final Set<ASTType> rtr = getInstantiations(tdecl);
		rtr.add(newType);
		return rtr;
	}

	@Override
	protected VarList processVarList(VarList vl) {
		final ASTType type = vl.getType();
		if (shouldFlatten(type) != null) {
			final ASTType newType = flatten(vl.getType(), null);
			if (newType != vl.getType()) {
				mLogger.info("Flattening " + BoogiePrettyPrinter.print(vl));
				return new VarList(vl.getLocation(), vl.getIdentifiers(), newType, vl.getWhereClause());
			} else {
				mVariablesToReplace.put(vl, newType);
				mLogger.info("Has to be flattened later " + BoogiePrettyPrinter.print(vl));
			}
		}
		return super.processVarList(vl);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		final TypeDeclaration decl = shouldFlatten(expr.getType());
		if (decl != null) {
			final ASTType newType = findInstantiation(decl, expr);

			if (expr instanceof IdentifierExpression && newType != null) {
				final ASTType sub = instantiateType(expr.getType(), newType);
				final String newIdentifier = getNewIdentifier(((IdentifierExpression) expr).getIdentifier(), decl, sub);
				mLogger.info("Instantiated " + BoogiePrettyPrinter.print(expr) + " with " + newIdentifier + " : "
						+ BoogiePrettyPrinter.print(sub));
				return new IdentifierExpression(expr.getLocation(), newIdentifier);
			} else {
				mLogger.info(
						"Should instantiate " + BoogiePrettyPrinter.print(expr) + " (" + expr.getClass().getSimpleName()
								+ ") with " + (newType == null ? "null" : BoogiePrettyPrinter.print(newType)));
			}
		}
		mExpressionStack.push(expr);
		final Expression rtr = super.processExpression(expr);
		mExpressionStack.pop();
		return rtr;
	}

	private ASTType instantiateType(IType type, ASTType substitute) {
		BoogieType bt = (BoogieType) type;
		return instantiateType(bt.toASTType(substitute.getLocation()), new ASTType[] { substitute });
	}

	private ASTType instantiateType(ASTType generic, ASTType[] params) {
		if (generic instanceof PrimitiveType) {
			return generic;
		} else if (generic instanceof NamedType) {
			NamedType namedGeneric = (NamedType) generic;
			ASTType[] typeargs = namedGeneric.getTypeArgs();
			if (typeargs.length != params.length) {
				if (typeargs.length == 0 && params.length == 1) {
					BoogieType bt = ((BoogieType) namedGeneric.getBoogieType());
					if (bt instanceof PlaceholderBoogieType) {
						return params[0];
					}
				}
				return generic;
			}

			if (params.length == 1) {
				return params[0];
			}
		} else if (generic instanceof ArrayType) {
			ArrayType arrayGeneric = (ArrayType) generic;
			if (arrayGeneric.getTypeParams().length != params.length) {
				return generic;
			}
			List<ASTType> newIdxTypes = new ArrayList<ASTType>();
			for (ASTType idxType : arrayGeneric.getIndexTypes()) {
				newIdxTypes.add(instantiateType(idxType, params));
			}
			ASTType newValueType = instantiateType(arrayGeneric.getValueType(), params);
			return new ArrayType(arrayGeneric.getLocation(), new String[0],
					newIdxTypes.toArray(new ASTType[newIdxTypes.size()]), newValueType);
		}
		throw new UnsupportedOperationException();
	}

	private String getNewIdentifier(final String oldId, final TypeDeclaration decl, final ASTType newType) {
		final String newId = oldId + "$" + getIdentifierSuffix(newType);
		final Declaration savedDecl = mNewGlobals.get(newId);
		if (savedDecl == null) {
			mNewGlobals.put(newId, new VariableDeclaration(decl.getLocation(), new Attribute[0],
					new VarList[] { new VarList(decl.getLocation(), new String[] { newId }, newType) }));
			// mNewGlobals.put(newId, new
			// TypeDeclaration(decl.getLocation(), new Attribute[0],
			// decl.isFinite(), newId,
			// new String[0], newType));
		}
		return newId;
	}

	private String getIdentifierSuffix(final ASTType type) {
		if (type instanceof PrimitiveType) {
			return ((PrimitiveType) type).getName();
		} else if (type instanceof ArrayType) {
			final ArrayType atype = (ArrayType) type;
			final StringBuilder sb = new StringBuilder();
			for (final ASTType idx : atype.getIndexTypes()) {
				sb.append(getIdentifierSuffix(idx)).append("$");
			}
			sb.append(getIdentifierSuffix(atype.getValueType()));
			return sb.toString();
		} else if (type instanceof NamedType) {
			return ((NamedType) type).getName();
		}
		throw new UnsupportedOperationException();
	}

	private ASTType findInstantiation(final TypeDeclaration decl, final Expression expr) {
		if (mExpressionStack.isEmpty()) {
			// we insert a fake type that will be expanded in a second pass
			// to all the other types we found (happens, i.e., for modifies)
			final ASTType newType = getFakeASTType(expr.getLocation());
			addInstantiation(decl, newType);
			return newType;
		}
		final ASTType synonym = decl.getSynonym();
		if (synonym != null) {
			// this type has a synonym, we have to check how we have to
			// flatten it
			if (synonym instanceof ArrayType) {
				ArrayType arraysyn = (ArrayType) synonym;
				BoogieType bt = (BoogieType) arraysyn.getBoogieType();

				ASTType newType = bt.substitutePlaceholders(null).toASTType(decl.getLocation());
				return newType;
			} else {
				throw new UnsupportedOperationException();
			}
		}

		return searchStack(decl);
	}

	private ASTType searchStack(final TypeDeclaration decl) throws AssertionError {
		ASTType newType = null;
		final Stack<Expression> restore = new Stack<Expression>();
		while (!mExpressionStack.isEmpty()) {
			final Expression parentExpr = mExpressionStack.pop();
			restore.push(parentExpr);

			if (shouldFlatten(parentExpr.getType()) != null) {
				continue;
			}
			final IType type = parentExpr.getType();
			if (!(type instanceof BoogieType)) {
				throw new AssertionError();
			}
			final BoogieType btype = (BoogieType) type;
			newType = btype.toASTType(parentExpr.getLocation());
			addInstantiation(decl, newType);
			break;
		}
		while (!restore.isEmpty()) {
			mExpressionStack.push(restore.pop());
		}
		return newType;
	}

	private ASTType getFakeASTType(final ILocation location) {
		return new FakeASTType(location);
	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		return super.processLeftHandSide(lhs);
	}

	private boolean isGeneric(final TypeDeclaration typeDecl) {
		final String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length != 0) {
			return true;
		}

		final ASTType synonyms = typeDecl.getSynonym();
		if (synonyms == null) {
			return false;
		}
		if (synonyms instanceof FakeASTType) {
			return true;
		}
		return isGeneric(synonyms);
	}

	private boolean isGeneric(final ASTType type) {
		if (type instanceof ArrayType) {
			final ArrayType atype = ((ArrayType) type);
			if (atype.getTypeParams().length != 0) {
				return true;
			}
			return isGeneric(atype.getValueType()) || Arrays.stream(atype.getIndexTypes()).anyMatch(this::isGeneric);
		} else if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			return Arrays.stream(ntype.getTypeArgs()).anyMatch(this::isGeneric);
		} else if (type instanceof StructType) {
			throw new UnsupportedOperationException("Structs should have been resolved already");
		} else if (type instanceof PrimitiveType) {
			return false;
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + type == null ? "null" : type.getClass().getSimpleName());
		}
	}

	private TypeDeclaration shouldFlatten(final ASTType type) {
		TypeDeclaration rtr;
		if (type instanceof ArrayType) {
			final ArrayType atype = ((ArrayType) type);
			rtr = shouldFlatten(atype.getValueType());
			if (rtr != null) {
				return rtr;
			}
			for (final ASTType idx : atype.getIndexTypes()) {
				rtr = shouldFlatten(idx);
				if (rtr != null) {
					return rtr;
				}
			}
		} else if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			rtr = shouldFlatten(ntype.getName());
			if (rtr != null) {
				return rtr;
			} else {
				for (ASTType arg : ntype.getTypeArgs()) {
					rtr = shouldFlatten(arg);
					if (rtr != null) {
						return rtr;
					}
				}
			}
		} else if (type instanceof StructType) {
			throw new UnsupportedOperationException("Structs should have been resolved already");
		} else if (type instanceof PrimitiveType) {
			final PrimitiveType ptype = ((PrimitiveType) type);
			// FIXME: probably always false ,)
			return shouldFlatten(ptype.getName());
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + type == null ? "null" : type.getClass().getSimpleName());
		}
		return null;
	}

	/**
	 * Returns null if the type is not generic, and a type definition that has
	 * to be instantiated for this type otherwise.
	 * 
	 * @param type
	 * @return
	 */
	private TypeDeclaration shouldFlatten(final IType type) {
		if (type instanceof BoogieType) {
			return shouldFlatten(((BoogieType) type).toASTType(null));
		} else if (type == null) {
			return null;
		} else {
			throw new UnsupportedOperationException("Unknown type " + type.getClass().getSimpleName());
		}
	}

	private TypeDeclaration shouldFlatten(final String name) {
		for (final Entry<TypeDeclaration, Set<ASTType>> ttf : mInstantiations.entrySet()) {
			if (ttf.getKey().getIdentifier().equals(name)) {
				return ttf.getKey();
			}
		}
		return null;
	}

	private ASTType flatten(final ASTType type, final ASTType[] params) {
		if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			if (ntype.getTypeArgs().length == 0) {
				return ntype;
			}
			if (ntype.getTypeArgs().length > 1) {
				throw new UnsupportedOperationException(
						"Cannot flatten named type with more than 1 type arg: " + ntype);
			}
			return ntype.getTypeArgs()[0];
		} else if (type instanceof ArrayType) {
			final ArrayType atype = (ArrayType) type;
			if (params == null || params.length != atype.getTypeParams().length) {
				throw new UnsupportedOperationException(
						"Cannot flatten array type without matching arguments: " + atype);
			}
			// TODO:
			return atype;
		} else {
			return type;
		}
	}
}