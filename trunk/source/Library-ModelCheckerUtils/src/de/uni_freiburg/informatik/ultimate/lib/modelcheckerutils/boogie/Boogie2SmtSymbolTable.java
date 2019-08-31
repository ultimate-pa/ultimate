/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ISmtDeclarable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.SmtFunctionDefinition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Stores a mapping from Boogie identifiers to BoogieVars and a mapping from TermVariables that are representatives of
 * BoogieVars to these BoogieVars.
 *
 * TODO 2018-09-15 Matthias: This class was build before we had {@link DeclarationInformation} and might be
 * unnecessarily complicated.
 *
 * @author Matthias Heizmann
 *
 */
public class Boogie2SmtSymbolTable
		implements IIcfgSymbolTable, IBoogieSymbolTableVariableProvider, ITerm2ExpressionSymbolTable {
	/**
	 * Identifier of attribute that we use to state that
	 * <ul>
	 * <li>no function has to be declared, function is already defined in the logic
	 * <li>given value has to be used in the translation.
	 * </ul>
	 *
	 */
	public static final String ID_BUILTIN = "builtin";

	/**
	 * Identifier of attribute that we use to declare a function symbol that should be mapped to an SMT term
	 */
	public static final String ID_SMTDEFINED = "smtdefined";

	private static final String ID_INDICES = "indices";

	private final BoogieDeclarations mBoogieDeclarations;
	private final ManagedScript mScript;
	private final TypeSortTranslator mTypeSortTranslator;
	private final Map<String, BoogieNonOldVar> mGlobals = new HashMap<>();
	private final Map<String, BoogieOldVar> mOldGlobals = new HashMap<>();
	private final Map<String, Map<String, IProgramVar>> mSpecificationInParam = new HashMap<>();
	private final Map<String, Map<String, IProgramVar>> mSpecificationOutParam = new HashMap<>();
	private final Map<String, Map<String, IProgramVar>> mImplementationInParam = new HashMap<>();
	private final Map<String, Map<String, IProgramVar>> mImplementationOutParam = new HashMap<>();
	private final Map<String, List<ILocalProgramVar>> mProc2InParams = new HashMap<>();
	private final Map<String, List<ILocalProgramVar>> mProc2OutParams = new HashMap<>();
	private final Map<String, Map<String, LocalBoogieVar>> mImplementationLocals = new HashMap<>();
	private final Map<String, BoogieConst> mConstants = new HashMap<>();

	private final Map<TermVariable, IProgramVar> mSmtVar2BoogieVar = new HashMap<>();
	private final Map<IProgramVar, DeclarationInformation> mBoogieVar2DeclarationInformation = new HashMap<>();
	private final Map<IProgramVar, BoogieASTNode> mBoogieVar2AstNode = new HashMap<>();
	private final Map<ApplicationTerm, BoogieConst> mSmtConst2BoogieConst = new HashMap<>();

	private final Map<String, String> mBoogieFunction2SmtFunction = new HashMap<>();
	private final Map<String, String> mSmtFunction2BoogieFunction = new HashMap<>();
	private final Map<String, Map<String, Expression[]>> mBoogieFunction2Attributes = new HashMap<>();

	private final DefaultIcfgSymbolTable mIcfgSymbolTable = new DefaultIcfgSymbolTable();

	public Boogie2SmtSymbolTable(final BoogieDeclarations boogieDeclarations, final ManagedScript script,
			final TypeSortTranslator typeSortTranslator) {
		mScript = script;
		mTypeSortTranslator = typeSortTranslator;
		mBoogieDeclarations = boogieDeclarations;

		mScript.lock(this);
		mScript.echo(this, new QuotedObject("Start declaration of constants"));
		for (final ConstDeclaration decl : mBoogieDeclarations.getConstDeclarations()) {
			declareConstants(decl);
		}
		mScript.echo(this, new QuotedObject("Finished declaration of constants"));

		mScript.echo(this, new QuotedObject("Start declaration of functions"));
		for (final FunctionDeclaration decl : mBoogieDeclarations.getFunctionDeclarations()) {
			declareFunction(decl);
		}
		mScript.echo(this, new QuotedObject("Finished declaration of functions"));

		mScript.echo(this, new QuotedObject("Start declaration of global variables"));
		for (final VariableDeclaration decl : mBoogieDeclarations.getGlobalVarDeclarations()) {
			declareGlobalVariables(decl);
		}
		mScript.echo(this, new QuotedObject("Finished declaration global variables"));

		mScript.echo(this, new QuotedObject("Start declaration of local variables"));
		for (final String procId : mBoogieDeclarations.getProcSpecification().keySet()) {
			final Procedure procSpec = mBoogieDeclarations.getProcSpecification().get(procId);
			final Procedure procImpl = mBoogieDeclarations.getProcImplementation().get(procId);
			if (procImpl == null) {
				declareSpec(procSpec);
			} else {
				declareSpecImpl(procSpec, procImpl);
			}
		}
		mScript.echo(this, new QuotedObject("Finished declaration local variables"));
		mScript.unlock(this);
	}

	private static <T extends IProgramVar> void putNew(final String procId, final String varId, final T bv,
			final Map<String, Map<String, T>> map) {
		Map<String, T> varId2BoogieVar = map.get(procId);
		if (varId2BoogieVar == null) {
			varId2BoogieVar = new HashMap<>();
			map.put(procId, varId2BoogieVar);
		}
		final IProgramVar previousValue = varId2BoogieVar.put(varId, bv);
		assert previousValue == null : "variable already contained";
	}

	private static <VALUE> void putNew(final String varId, final VALUE value, final Map<String, VALUE> map) {
		final VALUE previousValue = map.put(varId, value);
		assert previousValue == null : "variable already contained";
	}

	private static <T extends IProgramVar> T get(final String varId, final String procId,
			final Map<String, Map<String, T>> map) {
		final Map<String, T> varId2BoogieVar = map.get(procId);
		if (varId2BoogieVar == null) {
			return null;
		}
		return varId2BoogieVar.get(varId);
	}

	public static boolean isSpecification(final Procedure spec) {
		return spec.getSpecification() != null;
	}

	public static boolean isImplementation(final Procedure impl) {
		return impl.getBody() != null;
	}

	@Override
	public IProgramVar getBoogieVar(final String varId, final DeclarationInformation declarationInformation,
			final boolean inOldContext) {
		final StorageClass storageClass = declarationInformation.getStorageClass();
		final String procedure = declarationInformation.getProcedure();
		switch (storageClass) {
		case GLOBAL:
			if (inOldContext) {
				return mOldGlobals.get(varId);
			}
			return mGlobals.get(varId);
		case PROC_FUNC_INPARAM:
		case IMPLEMENTATION_INPARAM:
			return get(varId, procedure, mImplementationInParam);
		case PROC_FUNC_OUTPARAM:
		case IMPLEMENTATION_OUTPARAM:
			return get(varId, procedure, mImplementationOutParam);
		case LOCAL:
			return get(varId, procedure, mImplementationLocals);
		case IMPLEMENTATION:
		case PROC_FUNC:
		case QUANTIFIED:
		default:
			throw new AssertionError("inappropriate decl info " + declarationInformation);
		}
	}

	/**
	 * Get IProgramVar for in our outparams.
	 *
	 * @param varId
	 *            The id of the param.
	 * @param procedure
	 *            The procedure.
	 * @param isInParam
	 *            true iff its an inparam, false if its an outparam.
	 * @return The IProgramVar.
	 */
	@Override
	public IProgramVar getBoogieVar(final String varId, final String procedure, final boolean isInParam) {
		if (isInParam) {
			return get(varId, procedure, mImplementationInParam);
		}
		return get(varId, procedure, mImplementationOutParam);
	}

	@Override
	public IProgramVar getProgramVar(final TermVariable tv) {
		return mIcfgSymbolTable.getProgramVar(tv);
	}

	@Override
	public DeclarationInformation getDeclarationInformation(final IProgramVar bv) {
		return mBoogieVar2DeclarationInformation.get(bv);
	}

	public BoogieASTNode getAstNode(final IProgramVar bv) {
		return mBoogieVar2AstNode.get(bv);
	}

	private void declareConstants(final ConstDeclaration constdecl) {
		final VarList varlist = constdecl.getVarList();
		final IBoogieType iType = varlist.getType().getBoogieType();
		final Map<String, Expression[]> attributes = extractAttributes(constdecl);
		if (attributes != null) {
			final String attributeDefinedIdentifier = checkForAttributeDefinedIdentifier(attributes, ID_BUILTIN);
			if (attributeDefinedIdentifier != null) {
				if (varlist.getIdentifiers().length > 1) {
					throw new IllegalArgumentException(
							"if builtin identifier is " + "used we support only one constant per const declaration");
				}
				final String constId = varlist.getIdentifiers()[0];
				final BigInteger[] indices = Boogie2SmtSymbolTable.checkForIndices(attributes);
				final ApplicationTerm constant =
						(ApplicationTerm) mScript.term(this, attributeDefinedIdentifier, indices, null);
				final BoogieConst boogieConst = new BoogieConst(constId, iType, constant, true);
				final BoogieConst previousValue = mConstants.put(constId, boogieConst);
				assert previousValue == null : "constant already contained";
				mSmtConst2BoogieConst.put(constant, boogieConst);
				mIcfgSymbolTable.add(boogieConst);
				return;
			}
		}
		final Sort[] paramTypes = new Sort[0];
		final Sort sort = mTypeSortTranslator.getSort(iType, varlist);
		for (final String constId : varlist.getIdentifiers()) {
			mScript.declareFun(this, constId, paramTypes, sort);
			final ApplicationTerm constant = (ApplicationTerm) mScript.term(this, constId);
			final BoogieConst boogieConst = new BoogieConst(constId, iType, constant, false);
			final BoogieConst previousValue = mConstants.put(constId, boogieConst);
			assert previousValue == null : "constant already contained";
			mSmtConst2BoogieConst.put(constant, boogieConst);
			mIcfgSymbolTable.add(boogieConst);
		}
	}

	@Override
	public BoogieConst getBoogieConst(final String constId) {
		return mConstants.get(constId);
	}

	@Override
	public BoogieConst getProgramConst(final ApplicationTerm smtConstant) {
		return (BoogieConst) mIcfgSymbolTable.getProgramConst(smtConstant);
	}

	public Map<String, Expression[]> getAttributes(final String boogieFunctionId) {
		return Collections.unmodifiableMap(mBoogieFunction2Attributes.get(boogieFunctionId));
	}

	private void declareFunction(final FunctionDeclaration funcdecl) {
		final Map<String, Expression[]> attributes = extractAttributes(funcdecl);
		final String id = funcdecl.getIdentifier();
		mBoogieFunction2Attributes.put(id, attributes);
		final String attributeDefinedIdentifier = checkForAttributeDefinedIdentifier(attributes, ID_BUILTIN);
		final String smtDefinedBody = checkForAttributeDefinedIdentifier(attributes, ID_SMTDEFINED);
		final String smtID;
		if (attributeDefinedIdentifier == null) {
			smtID = Boogie2SMT.quoteId(id);
		} else {
			smtID = attributeDefinedIdentifier;
			if (smtDefinedBody != null) {
				throw new ISmtDeclarable.IllegalSmtDeclarableUsageException(
						id + " has " + ID_SMTDEFINED + " and " + ID_BUILTIN + " attributes");
			}
		}
		int numParams = 0;
		for (final VarList vl : funcdecl.getInParams()) {
			final int ids = vl.getIdentifiers().length;
			numParams += ids == 0 ? 1 : ids;
		}

		final Sort[] paramSorts = new Sort[numParams];
		final String[] paramIds = new String[numParams];
		int paramNr = 0;
		for (final VarList vl : funcdecl.getInParams()) {
			int ids = vl.getIdentifiers().length;
			if (ids == 0) {
				ids = 1;
			}
			final IBoogieType paramType = vl.getType().getBoogieType();
			final Sort paramSort = mTypeSortTranslator.getSort(paramType, funcdecl);
			for (int i = 0; i < ids; i++) {
				paramSorts[paramNr] = paramSort;
				if (i < vl.getIdentifiers().length) {
					paramIds[paramNr] = vl.getIdentifiers()[i];
				} else {
					paramIds[paramNr] = null;
				}
				paramNr++;
			}
		}
		final IBoogieType resultType = funcdecl.getOutParam().getType().getBoogieType();
		final Sort resultSort = mTypeSortTranslator.getSort(resultType, funcdecl);
		if (attributeDefinedIdentifier == null) {
			// no builtin function, we have to declare it
			final SmtFunctionDefinition smtFunctionDefinition = SmtFunctionDefinition
					.createFromString(mScript.getScript(), smtID, smtDefinedBody, paramIds, paramSorts, resultSort);
			smtFunctionDefinition.defineOrDeclare(mScript.getScript());
		}
		mBoogieFunction2SmtFunction.put(id, smtID);
		mSmtFunction2BoogieFunction.put(smtID, id);
	}

	/**
	 * Returns the single StringLiteral value of the NamedAttribute with name n. Throws an IllegalArgumentException if
	 * there is a NamedAttribute with name whose value is not a single StringLiteral. Returns null if there is no
	 * NamedAttribute with name n.
	 */
	public static String checkForAttributeDefinedIdentifier(final Map<String, Expression[]> attributes,
			final String n) {
		final Expression[] values = attributes.get(n);
		if (values == null) {
			// no such name
			return null;
		}
		if (values.length == 1 && values[0] instanceof StringLiteral) {
			final StringLiteral sl = (StringLiteral) values[0];
			return sl.getValue();
		}
		throw new IllegalArgumentException("Attribute has more than one argument or argument is not String: " + n);
	}

	/**
	 * Checks if there is an annotation with the name {@link #ID_INDICES} According to our convention this attribute
	 * defines the indices for the corresponding SMT function. Returns the array of indices if there is an attribute
	 * with this name and null otherwise.
	 */
	public static BigInteger[] checkForIndices(final Map<String, Expression[]> attributes) {
		final Expression[] values = attributes.get(ID_INDICES);
		if (values == null) {
			// no such name
			return null;
		}
		final BigInteger[] result = new BigInteger[values.length];
		for (int i = 0; i < values.length; i++) {
			if (values[i] instanceof IntegerLiteral) {
				result[i] = new BigInteger(((IntegerLiteral) values[i]).getValue());
			} else {
				throw new IllegalArgumentException("no single value attribute");
			}
		}
		return result;
	}

	public static Map<String, Expression[]> extractAttributes(final Declaration decl) {
		final Map<String, Expression[]> result = new HashMap<>();
		for (final Attribute attr : decl.getAttributes()) {
			if (attr instanceof NamedAttribute) {
				final NamedAttribute nattr = (NamedAttribute) attr;
				result.put(nattr.getName(), ((NamedAttribute) attr).getValues());
			}
		}
		return result;
	}

	@Override
	public Map<String, String> getSmtFunction2BoogieFunction() {
		return Collections.unmodifiableMap(mSmtFunction2BoogieFunction);
	}

	public Map<String, String> getBoogieFunction2SmtFunction() {
		return Collections.unmodifiableMap(mBoogieFunction2SmtFunction);
	}

	private void declareGlobalVariables(final VariableDeclaration vardecl) {
		for (final VarList vl : vardecl.getVariables()) {
			for (final String id : vl.getIdentifiers()) {
				final IBoogieType type = vl.getType().getBoogieType();
				final BoogieNonOldVar global = constructGlobalBoogieVar(id, type, vl);
				putNew(id, global, mGlobals);
				final BoogieOldVar oldGlobal = global.getOldVar();
				putNew(id, oldGlobal, mOldGlobals);
			}
		}
	}

	@Override
	public Set<IProgramNonOldVar> getGlobals() {
		return mIcfgSymbolTable.getGlobals();
	}

	/**
	 * Return global variables;
	 *
	 * @return Map that assigns to each variable identifier the non-old global variable
	 */
	public Map<String, IProgramNonOldVar> getGlobalsMap() {
		return Collections.unmodifiableMap(mGlobals);
	}

	/**
	 * Return old variables.
	 */
	public Map<String, IProgramVar> getOldVars() {
		return Collections.unmodifiableMap(mOldGlobals);
	}

	@Override
	public Set<ILocalProgramVar> getLocals(final String proc) {
		return mIcfgSymbolTable.getLocals(proc);
	}

	@Override
	public Set<IProgramConst> getConstants() {
		return mIcfgSymbolTable.getConstants();
	}

	/**
	 * Return global constants;
	 */
	public Map<String, BoogieConst> getConstsMap() {
		return Collections.unmodifiableMap(mConstants);
	}

	private void declareSpecImpl(final Procedure spec, final Procedure impl) {
		final String procId = spec.getIdentifier();
		assert procId.equals(impl.getIdentifier());
		DeclarationInformation declInfoInParam;
		DeclarationInformation declInfoOutParam;
		if (spec == impl) {
			// implementation is given in procedure declaration, in this case
			// we consider all in/out-params as procedure variables
			declInfoInParam = new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procId);
			declInfoOutParam = new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procId);
		} else {
			assert isSpecAndImpl(spec, impl);
			// implementation is given in a separate declaration, in this case
			// we consider all in/out-params as implementation variables
			declInfoInParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procId);
			declInfoOutParam = new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, procId);

		}
		declareParams(procId, spec.getInParams(), impl.getInParams(), mSpecificationInParam, mImplementationInParam,
				declInfoInParam, mProc2InParams);
		declareParams(procId, spec.getOutParams(), impl.getOutParams(), mSpecificationOutParam, mImplementationOutParam,
				declInfoOutParam, mProc2OutParams);
		declareLocals(impl);
	}

	/**
	 * Returns true if spec contains only a specification or impl contains only an implementation.
	 */
	private static boolean isSpecAndImpl(final Procedure spec, final Procedure impl) {
		return isSpecification(spec) && !isImplementation(spec) && isImplementation(impl) && !isSpecification(impl);

	}

	private void declareSpec(final Procedure spec) {
		assert isSpecification(spec) : "no specification";
		assert !isImplementation(spec) : "is implementation";
		final String procId = spec.getIdentifier();
		declareParams(procId, spec.getInParams(), mSpecificationInParam,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procId), mProc2InParams);
		declareParams(procId, spec.getOutParams(), mSpecificationOutParam,
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procId), mProc2OutParams);
	}

	private void declareParams(final String procId, final VarList[] specVl, final VarList[] implVl,
			final Map<String, Map<String, IProgramVar>> specMap, final Map<String, Map<String, IProgramVar>> implMap,
			final DeclarationInformation declarationInformation,
			final Map<String, List<ILocalProgramVar>> proc2params) {
		if (specVl.length != implVl.length) {
			throw new IllegalArgumentException("specification and implementation have different param length");
		}
		final List<ILocalProgramVar> params = new ArrayList<>();
		final List<ILocalProgramVar> previous = proc2params.put(procId, Collections.unmodifiableList(params));
		if (previous != null) {
			throw new AssertionError("params for procedure " + procId + " already added");
		}
		for (int i = 0; i < specVl.length; i++) {
			final IBoogieType specType = specVl[i].getType().getBoogieType();
			final IBoogieType implType = implVl[i].getType().getBoogieType();
			if (!specType.equals(implType)) {
				throw new IllegalArgumentException("specification and implementation have different types");
			}
			final String[] specIds = specVl[i].getIdentifiers();
			final String[] implIds = implVl[i].getIdentifiers();
			if (specIds.length != implIds.length) {
				throw new IllegalArgumentException("specification and implementation have different param length");
			}
			for (int j = 0; j < specIds.length; j++) {
				final LocalBoogieVar bv =
						constructLocalBoogieVar(implIds[j], procId, implType, implVl[i], declarationInformation);
				putNew(procId, implIds[j], bv, implMap);
				putNew(procId, specIds[j], bv, specMap);
				params.add(bv);
			}
		}
	}

	/**
	 * Declare in or our parameters of a specification.
	 *
	 * @param procId
	 *            name of procedure
	 * @param vl
	 *            Varlist defining the parameters
	 * @param specMap
	 *            map for the specification
	 * @param declarationInformation
	 *            StorageClass of the constructed IProgramVar
	 */
	private void declareParams(final String procId, final VarList[] vl,
			final Map<String, Map<String, IProgramVar>> specMap, final DeclarationInformation declarationInformation,
			final Map<String, List<ILocalProgramVar>> proc2params) {
		final ArrayList<ILocalProgramVar> params = new ArrayList<>();
		final List<ILocalProgramVar> previous = proc2params.put(procId, Collections.unmodifiableList(params));
		if (previous != null) {
			throw new AssertionError("params for procedure " + procId + " already added");
		}
		for (int i = 0; i < vl.length; i++) {
			final IBoogieType type = vl[i].getType().getBoogieType();
			final String[] ids = vl[i].getIdentifiers();
			for (int j = 0; j < ids.length; j++) {
				final LocalBoogieVar bv = constructLocalBoogieVar(ids[j], procId, type, vl[i], declarationInformation);
				putNew(procId, ids[j], bv, specMap);
				params.add(bv);
			}
		}
	}

	public void declareLocals(final Procedure proc) {
		if (proc.getBody() != null) {
			final DeclarationInformation declarationInformation =
					new DeclarationInformation(StorageClass.LOCAL, proc.getIdentifier());
			for (final VariableDeclaration vdecl : proc.getBody().getLocalVars()) {
				for (final VarList vl : vdecl.getVariables()) {
					for (final String id : vl.getIdentifiers()) {
						final IBoogieType type = vl.getType().getBoogieType();
						final LocalBoogieVar bv =
								constructLocalBoogieVar(id, proc.getIdentifier(), type, vl, declarationInformation);
						putNew(proc.getIdentifier(), id, bv, mImplementationLocals);
					}
				}
			}
		}
	}

	/**
	 * Construct IProgramVar and store it. Expects that no IProgramVar with the same identifier has already been
	 * constructed.
	 *
	 * @param identifier
	 * @param procedure
	 * @param iType
	 * @param isOldvar
	 * @param boogieASTNode
	 *            BoogieASTNode for which errors (e.g., unsupported syntax) are reported
	 * @param declarationInformation
	 */
	public LocalBoogieVar constructLocalBoogieVar(final String identifier, final String procedure,
			final IBoogieType iType, final VarList varList, final DeclarationInformation declarationInformation) {
		final Sort sort = mTypeSortTranslator.getSort(iType, varList);

		final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, false, false);

		final TermVariable termVariable = mScript.variable(name, sort);

		final ApplicationTerm defaultConstant = ProgramVarUtils.constructDefaultConstant(mScript, this, sort, name);
		final ApplicationTerm primedConstant = ProgramVarUtils.constructPrimedConstant(mScript, this, sort, name);

		final LocalBoogieVar bv =
				new LocalBoogieVar(identifier, procedure, iType, termVariable, defaultConstant, primedConstant);

		mSmtVar2BoogieVar.put(termVariable, bv);
		mBoogieVar2DeclarationInformation.put(bv, declarationInformation);
		mBoogieVar2AstNode.put(bv, varList);
		mIcfgSymbolTable.add(bv);
		return bv;
	}

	/**
	 * Construct global IProgramVar and the corresponding oldVar and store both. Expects that no local BoogieVarwith the
	 * same identifier has already been constructed.
	 *
	 * @param boogieASTNode
	 *            BoogieASTNode for which errors (e.g., unsupported syntax) are reported
	 */
	private BoogieNonOldVar constructGlobalBoogieVar(final String identifier, final IBoogieType iType,
			final VarList varlist) {
		final Sort sort = mTypeSortTranslator.getSort(iType, varlist);
		final DeclarationInformation declarationInformation = new DeclarationInformation(StorageClass.GLOBAL, null);

		final BoogieNonOldVar nonOldVar =
				ProgramVarUtils.constructGlobalProgramVarPair(identifier, sort, mScript, this);
		mSmtVar2BoogieVar.put(nonOldVar.getTermVariable(), nonOldVar);
		mBoogieVar2DeclarationInformation.put(nonOldVar, declarationInformation);
		mBoogieVar2AstNode.put(nonOldVar, varlist);

		final BoogieOldVar oldVar = nonOldVar.getOldVar();
		mSmtVar2BoogieVar.put(oldVar.getTermVariable(), oldVar);
		mBoogieVar2DeclarationInformation.put(oldVar, declarationInformation);
		mBoogieVar2AstNode.put(oldVar, varlist);

		mIcfgSymbolTable.add(nonOldVar);
		return nonOldVar;
	}

	public HashRelation<String, IProgramNonOldVar> constructProc2ModifiableGlobalsMapping() {
		final HashRelation<String, IProgramNonOldVar> result = new HashRelation<>();
		for (final Entry<String, Set<String>> proc2vars : mBoogieDeclarations.getModifiedVars().entrySet()) {
			for (final String var : proc2vars.getValue()) {
				final IProgramNonOldVar pv = getGlobalsMap().get(var);
				result.addPair(proc2vars.getKey(), pv);
			}
		}

		// assume that add auxVar are modifiable by all procedures
		final Set<String> procedures = new HashSet<>();
		for (final String procId : mSpecificationInParam.keySet()) {
			procedures.add(procId);
		}
		for (final String procId : mImplementationInParam.keySet()) {
			procedures.add(procId);
		}

		return result;
	}

	@Override
	public ILocation getLocation(final IProgramVar pv) {
		final BoogieASTNode astNode = getAstNode(pv);
		assert astNode != null : "There is no AstNode for the IProgramVar " + pv;
		final ILocation loc = astNode.getLocation();
		return loc;
	}

	public Map<String, List<ILocalProgramVar>> getProc2InParams() {
		return Collections.unmodifiableMap(mProc2InParams);
	}

	public Map<String, List<ILocalProgramVar>> getProc2OutParams() {
		return Collections.unmodifiableMap(mProc2OutParams);
	}

	@Override
	public Set<ApplicationTerm> computeAllDefaultConstants() {
		final Set<ApplicationTerm> rtr = new LinkedHashSet<>();
		final Function<IProgramVar, ApplicationTerm> fun = IProgramVar::getDefaultConstant;
		getAll(mSpecificationInParam, fun).forEachOrdered(rtr::add);
		getAll(mSpecificationOutParam, fun).forEachOrdered(rtr::add);
		getAll(mImplementationInParam, fun).forEachOrdered(rtr::add);
		getAll(mImplementationOutParam, fun).forEachOrdered(rtr::add);
		mImplementationLocals.entrySet().stream().flatMap(a -> a.getValue().entrySet().stream())
				.map(a -> fun.apply(a.getValue())).forEachOrdered(rtr::add);
		mProc2InParams.entrySet().stream().flatMap(a -> a.getValue().stream()).map(fun::apply).forEachOrdered(rtr::add);
		mProc2OutParams.entrySet().stream().flatMap(a -> a.getValue().stream()).map(fun::apply)
				.forEachOrdered(rtr::add);
		mGlobals.entrySet().stream().map(a -> fun.apply(a.getValue())).forEachOrdered(rtr::add);
		mOldGlobals.entrySet().stream().map(a -> fun.apply(a.getValue())).forEachOrdered(rtr::add);
		return rtr;
	}

	private static <V, T, K1, K2> Stream<T> getAll(final Map<K1, Map<K2, V>> map, final Function<V, T> fun) {
		return map.entrySet().stream().flatMap(a -> a.getValue().entrySet().stream()).map(a -> fun.apply(a.getValue()));
	}
}
