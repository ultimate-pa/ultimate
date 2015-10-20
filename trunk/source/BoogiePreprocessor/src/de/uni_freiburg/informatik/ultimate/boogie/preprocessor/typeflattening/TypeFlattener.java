package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
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
import de.uni_freiburg.informatik.ultimate.boogie.type.TypeConstructor;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
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
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

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
	private final Map<StructConstructor, BoogieType> mStructConsts2BoogieTypes;
	private final Map<BoogieType, StructBoogieType> mOld2NewArrayTypes;
	private final ScopedHashMap<String, BoogieType> mVarnames2NewTypes;

	private final Set<String> mNewType;
	private final Map<ASTType, ASTType> mOld2NewAstTypes;
	private final Map<BoogieType, BoogieType> mOld2NewBoogieTypes;

	TypeFlattener(final Logger logger) {
		mLogger = logger;
		mGenericTypeDeclarations = new LinkedHashMap<>();
		mGenericType2InstantiatedTypes = new HashMap<BoogieType, Set<BoogieType>>();
		mGenericType2Vars = new HashMap<BoogieType, Set<PlaceholderVarList>>();
		mStructConsts2BoogieTypes = new HashMap<StructConstructor, BoogieType>();
		mOld2NewArrayTypes = new HashMap<BoogieType, StructBoogieType>();
		mVarnames2NewTypes = new ScopedHashMap<String, BoogieType>();
		mNewType = new HashSet<>();
		mOld2NewBoogieTypes = new HashMap<>();
		mOld2NewAstTypes = new HashMap<>();
	}

	void run(final Unit unit) {

		final ExposedTransformer[] transformers = new ExposedTransformer[] { 
//				new InstantiateUninterpretedTypes(),
				new InstantiateInterpretedTypes() 
				};

		List<Declaration> newdecls = new ArrayList<>();
		List<Declaration> olddecls = new ArrayList<>();
		olddecls.addAll(Arrays.asList(unit.getDeclarations()));

		for (final ExposedTransformer transformer : transformers) {
			mLogger.info("Run " + transformer.getClass().getSimpleName());
			for (final Declaration decl : olddecls) {
				final Declaration newdecl = transformer.processDeclaration(decl);
				if (newdecl != null) {
					newdecls.add(newdecl);
				}
			}
			transformer.finish(newdecls);
			olddecls = newdecls;
			newdecls = new ArrayList<Declaration>();
		}

		mLogger.info("Consolidate");
		consolidateMaps();

		olddecls = newdecls;
		newdecls = new ArrayList<Declaration>();
		mLogger.info("Second run");
		final DeclareNewTypes second = new DeclareNewTypes();
		for (final Declaration decl : olddecls) {
			final Collection<Declaration> result = second.process(decl);
			if (result != null) {
				newdecls.addAll(result);
			}
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

	private String prettyPrintTyped(IdentifierExpression iexpr) {
		return iexpr.getIdentifier() + " (" + iexpr.getType() + ")";
	}

	private static class ExposedTransformer extends BoogieTransformer {
		@Override
		protected Declaration processDeclaration(Declaration decl) {
			return super.processDeclaration(decl);
		}

		protected void finish(List<Declaration> decls) {

		}
	}

	private final class InstantiateUninterpretedTypes extends ExposedTransformer {

		@Override
		protected Declaration processDeclaration(Declaration decl) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				if (tdecl.getSynonym() == null && isGeneric(tdecl)) {
					mLogger.info("Deleted declaration " + BoogiePrettyPrinter.print(tdecl));
					return null;
				}
			}
			return super.processDeclaration(decl);
		}

		@Override
		protected VarList processVarList(VarList vl) {
			final ASTType oldtype = vl.getType();
			if (!isGeneric(oldtype)) {
				return super.processVarList(vl);
			}

			final ASTType newtype = getNewType(oldtype);
			if (newtype == null) {
				return super.processVarList(vl);
			}

			final VarList rtr = new VarList(vl.getLocation(), vl.getIdentifiers(), newtype, vl.getWhereClause());
			mLogger.info("Replaced varlist " + BoogiePrettyPrinter.print(vl) + " with " + BoogiePrettyPrinter.print(rtr));
			return rtr;
		}

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression iexpr = (IdentifierExpression) expr;
				final BoogieType oldtype = (BoogieType) iexpr.getType();
				final BoogieType newtype = mOld2NewBoogieTypes.get(oldtype);
				if (newtype != null) {
					final IdentifierExpression rtr = new IdentifierExpression(expr.getLocation(), newtype,
							iexpr.getIdentifier(), iexpr.getDeclarationInformation());
					mLogger.info("Replaced expr " + prettyPrintTyped(iexpr) + " with " + prettyPrintTyped(rtr));
					return rtr;
				}
			}
			return super.processExpression(expr);
		}

		@Override
		protected ASTType processType(ASTType oldtype) {
			if (!isGeneric(oldtype)) {
				return super.processType(oldtype);
			}

			final ASTType newtype = getNewType(oldtype);
			if (newtype == null) {
				return super.processType(oldtype);
			}
			mLogger.info(
					"Replaced type " + BoogiePrettyPrinter.print(oldtype) + " with " + BoogiePrettyPrinter.print(newtype));
			return newtype;
		}

		private ASTType getNewType(final ASTType oldtype) {
			final ASTType newtype = flatten(oldtype);
			if (newtype == null) {
				// cannot flatten now, do it later
				return null;
			}
			final String uninterpretedTypeName = BoogiePrettyPrinter.print(newtype);
			mOld2NewAstTypes.put(oldtype, newtype);

			final BoogieType oldboogietype = (BoogieType) oldtype.getBoogieType();
			final BoogieType newboogietype = BoogieType
					.createConstructedType(new TypeConstructor(uninterpretedTypeName, false, 0, new int[0]));
			mOld2NewBoogieTypes.put(oldboogietype, newboogietype);

			mNewType.add(uninterpretedTypeName);
			return newtype;
		}

		@Override
		protected void finish(List<Declaration> decls) {
			// just adding new uninterpreted types (from the instantiation of
			// uninterpreted types)
			for (final String name : mNewType) {
				decls.add(0, new TypeDeclaration(null, new Attribute[0], false, name, new String[0]));
			}
		}
	}

	private final class InstantiateInterpretedTypes extends ExposedTransformer {

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				if (isGeneric(tdecl)) {
					mLogger.info("Replaced " + BoogiePrettyPrinter.print(tdecl) + " with placeholder");
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
				final PlaceholderVarList rtr = new PlaceholderVarList(vl);
				BoogieType bt = (BoogieType) vl.getType().getBoogieType();
				markGenericType(bt, rtr);
				mLogger.info("Replaced " + BoogiePrettyPrinter.print(vl) + " with placeholder");
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
					mLogger.info("Instantiated " + genericType + " with " + newArrayType);

					final Expression arrayExpr = processExpression(aaexpr.getArray());

					final Expression rtr = new ArrayAccessExpression(expr.getLocation(), newArrayType,
							new StructAccessExpression(expr.getLocation(), null, arrayExpr,
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
					final Expression newValueExpr = processExpression(asexpr.getValue());

					final Expression arrayFromStructExpression = new StructAccessExpression(expr.getLocation(),
							newArrayType, newArrayExpr, getStructFieldName(newArrayType));

					final Expression newArrayStoreExpr = new ArrayStoreExpression(expr.getLocation(), newArrayType,
							arrayFromStructExpression, newIdxExpr, newValueExpr);

					// we have to fill in the actual struct type in a later run
					final StructConstructor rtr = new StructConstructor(expr.getLocation(), null,
							new String[] { getStructFieldName(newArrayType) }, new Expression[] { newArrayStoreExpr });
					mLogger.info(
							"Replaced " + BoogiePrettyPrinter.print(expr) + " with " + BoogiePrettyPrinter.print(rtr));
					mStructConsts2BoogieTypes.put(rtr, atype);
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

	private final class DeclareNewTypes extends BoogieTransformer {

		private Collection<Declaration> process(Declaration decl) {
			if (decl instanceof PlaceholderTypeDeclaration) {
				final Collection<Declaration> rtr = new ArrayList<Declaration>();
				final PlaceholderTypeDeclaration ptdecl = (PlaceholderTypeDeclaration) decl;
				final ASTType interpretedType = ptdecl.getSynonym();
				if (interpretedType != null) {
					if (interpretedType instanceof ArrayType) {
						final ILocation loc = ptdecl.getLocation();
						int size = ptdecl.mTypes.size();
						final VarList[] fields = new VarList[size];
						final String[] fNames = new String[size];
						final BoogieType[] fTypes = new BoogieType[size];

						int i = 0;
						for (final ASTType newType : ptdecl.mTypes) {
							fNames[i] = getFieldName(newType);
							fTypes[i] = (BoogieType) newType.getBoogieType();
							fields[i] = new VarList(loc, new String[] { fNames[i] }, newType);
							++i;
						}

						final StructBoogieType boogieType = BoogieType.createStructType(fNames, fTypes);

						final ASTType synonym = new StructType(loc, boogieType, fields);
						final TypeDeclaration newdecl = new TypeDeclaration(loc, ptdecl.getAttributes(),
								ptdecl.isFinite(), ptdecl.getIdentifier(), new String[0], synonym);
						mLogger.info("Declared " + BoogiePrettyPrinter.print(newdecl));
						mOld2NewArrayTypes.put((BoogieType) interpretedType.getBoogieType(), boogieType);
						rtr.add(newdecl);
					}
				} else {
					// all uninterpreted types are just named types
					for (final ASTType newType : ptdecl.mTypes) {
						final NamedType nt = (NamedType) newType;
						final TypeDeclaration newdecl = new TypeDeclaration(ptdecl.getLocation(),
								ptdecl.getAttributes(), ptdecl.isFinite(), nt.getName(), new String[0]);
						mLogger.info("Declared " + BoogiePrettyPrinter.print(newdecl));
						rtr.add(newdecl);
					}
				}
				return rtr;
			} else if (decl instanceof FunctionDeclaration || decl instanceof Procedure) {
				mVarnames2NewTypes.beginScope();
				final List<Declaration> rtr = Collections.singletonList(super.processDeclaration(decl));
				mVarnames2NewTypes.endScope();
				return rtr;
			}

			return Collections.singletonList(super.processDeclaration(decl));
		}

		@Override
		protected Body processBody(Body body) {
			mVarnames2NewTypes.beginScope();
			Body rtr = super.processBody(body);
			mVarnames2NewTypes.endScope();
			return rtr;
		}

		@Override
		protected VarList processVarList(VarList vl) {
			if (vl instanceof PlaceholderVarList) {
				final PlaceholderVarList phvl = ((PlaceholderVarList) vl);
				final ASTType type = phvl.getType();
				ASTType newtype = flatten(type);
				if (newtype == null) {
					// we probably replaced the parent, so lets just get that
					// one
					BoogieType oldBoogieType = ((BoogieType) type.getBoogieType()).getUnderlyingType();
					StructBoogieType newBoogieType = mOld2NewArrayTypes.get(oldBoogieType);
					newtype = newBoogieType.toASTType(vl.getLocation());
				} else {
					final BoogieType oldBoogieType = (BoogieType) type.getBoogieType();
					newtype.setBoogieType(BoogieType.createConstructedType(new TypeConstructor(
							((NamedType) newtype).getName(), oldBoogieType.isFinite(), 0, new int[0])));

				}
				final BoogieType bt = (BoogieType) newtype.getBoogieType();
				assert bt != null;
				final VarList newvl = new VarList(vl.getLocation(), vl.getIdentifiers(), newtype, vl.getWhereClause());
				for (final String id : vl.getIdentifiers()) {
					mVarnames2NewTypes.put(id, bt.getUnderlyingType());
				}
				mLogger.info("Declared " + BoogiePrettyPrinter.print(newvl));
				return newvl;
			}

			return super.processVarList(vl);
		}

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				final IdentifierExpression iexpr = (IdentifierExpression) expr;
				final BoogieType newtype = mVarnames2NewTypes.get(iexpr.getIdentifier());
				if (newtype != null) {
					mLogger.info("Changed type of identifier " + BoogiePrettyPrinter.print(iexpr) + ": "
							+ iexpr.getType() + " -> " + newtype);
					return new IdentifierExpression(expr.getLocation(), newtype, iexpr.getIdentifier(),
							iexpr.getDeclarationInformation());
				}

			} else if (expr instanceof StructConstructor) {
				return createStructConstructor((StructConstructor) expr);
			} else if (expr instanceof StructAccessExpression) {
				// replace all the wrong array types with the now known struct
				// type
				StructAccessExpression saexpr = (StructAccessExpression) expr;
				IType oldType = saexpr.getStruct().getType();
				if (oldType instanceof ArrayBoogieType) {
					// we did not know the real type at that time, now we know
					StructBoogieType newType = mOld2NewArrayTypes.get(oldType);
					saexpr.getStruct().setType(newType);
				}
				assert saexpr.getStruct().getType() instanceof StructBoogieType;
				return super.processExpression(expr);
			} else if (expr instanceof FunctionApplication || expr instanceof QuantifierExpression) {
				mVarnames2NewTypes.beginScope();
				Expression rtr = super.processExpression(expr);
				mVarnames2NewTypes.endScope();
				return rtr;
			}
			return super.processExpression(expr);
		}

		private String getFieldName(ASTType type) {
			return mangleTypeName(new StringBuilder(), (BoogieType) type.getBoogieType()).toString();
		}

		private StructConstructor createStructConstructor(final StructConstructor sconst) {
			final BoogieType oldBoogieType = mStructConsts2BoogieTypes.get(sconst);
			if (oldBoogieType == null) {
				// was non-generic struct, just ignore it
				return sconst;
			}

			final StructBoogieType newBoogieType = mOld2NewArrayTypes.get(oldBoogieType);

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
				String id = newBoogieType.getFieldIds()[i];
				BoogieType type = newBoogieType.getFieldType(i);
				fieldIdentifiers[i] = id;
				if (id.equals(tmpField)) {
					fieldValues[i] = tmpFieldValue;
				} else {
					fieldValues[i] = new StructAccessExpression(loc, type, struct, id);
				}
			}
			final StructConstructor rtr = new StructConstructor(loc, newBoogieType, fieldIdentifiers, fieldValues);
			mLogger.info("Finalized struct access with " + BoogiePrettyPrinter.print(rtr));
			return rtr;
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