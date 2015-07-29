package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizeConstants;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Collect function declarations for all functions that are used in the
 * translation.
 * During the translation we use one object of this class. The object provides
 * methods to construct function declarations. At the end of the translation
 * process all these function declarations should be added to the resulting
 * Boogie program.
 * @author Matthias Heizmann
 *
 */
public class FunctionDeclarations {
	
	/**
	 * Names of all bitwise operation that occurred in the program.
	 */
	private final LinkedHashMap<String, FunctionDeclaration> m_DeclaredFunctions = new LinkedHashMap<String, FunctionDeclaration>();
	private final ITypeHandler m_TypeHandler;
	private final TypeSizeConstants m_TypeSizeConstants;
	
	
	public FunctionDeclarations(ITypeHandler typeHandler,
			TypeSizeConstants typeSizeConstants) {
		super();
		m_TypeHandler = typeHandler;
		m_TypeSizeConstants = typeSizeConstants;
	}

	public void declareBitvectorFunction(ILocation loc, String prefixedFunctionName, CPrimitive resultCType, CPrimitive... paramCTypes) {
		if (!prefixedFunctionName.startsWith(SFO.AUXILIARY_FUNCTION_PREFIX)) {
			throw new IllegalArgumentException("Our convention says that user defined functions start with tilde");
		}
		CPrimitive firstParam = paramCTypes[0];
		Integer bytesize = m_TypeSizeConstants.getCPrimitiveToTypeSizeConstant().get(firstParam.getType());
		int bitsize = bytesize * 8;
		String functionName = prefixedFunctionName.substring(1, prefixedFunctionName.length());
		String prefixedfunctionNameWithSuffix = prefixedFunctionName + bitsize;
		Attribute attribute = new NamedAttribute(loc, "bvbuiltin", new Expression[] { new StringLiteral(loc, functionName) });
		Attribute[] attributes = new Attribute[] { attribute };
		declareFunction(loc, prefixedfunctionNameWithSuffix, attributes , resultCType, paramCTypes);
	}
	
	public void declareFunction(ILocation loc, String prefixedFunctionName, Attribute[] attributes, CType resultCType, CType... paramCTypes) {
		ASTType resultASTType = m_TypeHandler.ctype2asttype(loc, resultCType);
		ASTType[] paramASTTypes = new ASTType[paramCTypes.length];
		for (int i=0; i<paramCTypes.length; i++) {
			paramASTTypes[i] = m_TypeHandler.ctype2asttype(loc, paramCTypes[i]);
		}
		declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTTypes);
	}
	
	public void declareFunction(ILocation loc, String prefixedFunctionName, Attribute[] attributes, ASTType resultASTType, ASTType... paramASTTypes) {
		if (m_DeclaredFunctions.containsKey(prefixedFunctionName)) {
			return;
			//throw new IllegalArgumentException("Function " + functionName + " already declared");
		}
		if (!prefixedFunctionName.startsWith(SFO.AUXILIARY_FUNCTION_PREFIX)) {
			throw new IllegalArgumentException("Our convention says that user defined functions start with tilde");
		}

		VarList[] inParams = new VarList[paramASTTypes.length];
		for (int i=0; i<paramASTTypes.length; i++) {
			inParams[i] = new VarList(loc, new String[] { "in" + i }, paramASTTypes[i]);
		}
		VarList outParam = new VarList(loc, new String[] { "out" }, resultASTType);
		FunctionDeclaration d = new FunctionDeclaration(loc, attributes, prefixedFunctionName, new String[0], inParams, outParam);
		m_DeclaredFunctions.put(prefixedFunctionName, d);
	}

	public LinkedHashMap<String, FunctionDeclaration> getDeclaredFunctions() {
		return m_DeclaredFunctions;
	}
	
	

}
