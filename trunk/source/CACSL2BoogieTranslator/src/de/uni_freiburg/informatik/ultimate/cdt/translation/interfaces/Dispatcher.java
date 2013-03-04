/**
 * Describes a dispatcher.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces;

import java.text.ParseException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NextACSL;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IPreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ISideEffectHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.PossibleUnsoundnessWarningResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public abstract class Dispatcher {
    /**
     * The side effect handler.
     */
    public ISideEffectHandler sideEffectHandler;
    /**
     * The C+ACSL handler.
     */
    public ICHandler cHandler;
    /**
     * The Type handler.
     */
    public ITypeHandler typeHandler;
    /**
     * The ACSL handler.
     */
    public IACSLHandler acslHandler;
    /**
     * The Name handler.
     */
    public INameHandler nameHandler;
    /**
     * Holds the next ACSL node in the decorator tree.
     */
    public NextACSL nextAcsl;
    /**
     * The Preprocessor statement handler.
     */
    public IPreprocessorHandler preprocessorHandler;
    /**
     * Whether UltimateServices is informed about warnings.
     */
    protected static boolean notifyUltimate = true;
    /**
     * Translation from Boogie to C for traces and expressions.
     */
    protected final Backtranslator backtranslator;
    
    public Dispatcher(Backtranslator backtranslator) {
		this.backtranslator = backtranslator;
	}

    /**
     * Initializes the handler fields.
     */
    protected abstract void init();

    /**
     * Dispatch a given node to a specific handler.
     * 
     * @param node
     *            the node to dispatch
     * @return the result for the given node
     */
    public abstract Result dispatch(DecoratorNode node);

    /**
     * Dispatch a given C node to a specific handler.
     * 
     * @param node
     *            the node to dispatch
     * @return the result for the given node
     */
    public abstract Result dispatch(IASTNode node);

    /**
     * Dispatch a given C node to a specific handler.
     * 
     * @param node
     *            the node to dispatch.
     * @return the resulting translation.
     */
    public abstract Result dispatch(IASTPreprocessorStatement node);

    /**
     * Dispatch a given IType to a specific handler.
     * 
     * @param type
     *            the type to dispatch
     * @return the result for the given type.
     */
    public abstract InferredType dispatch(IType type);

    /**
     * Dispatch a given ACSL node to the specific handler.
     * 
     * @param node
     *            the node to dispatch
     * @return the result for the given node
     */
    public abstract Result dispatch(ACSLNode node);

    /**
     * Entry point for a translation.
     * 
     * @param node
     *            the root node from which the translation should be started
     * @return the result for the given node
     */
    public final Result run(DecoratorNode node) {
        preRun(node);
        init();
        return dispatch(node);
    }

    /**
     * The method implementing a pre-run, if required.
     * 
     * @param node
     *            the node for which the pre run should be started
     */
    protected abstract void preRun(DecoratorNode node);

    /**
     * Iterates to the next ACSL statement in the decorator tree and returns a
     * list of ACSL nodes until the next C node appears.
     * 
     * @return a list of ACSL nodes until the next C node appears.
     * @throws ParseException
     *             if no trailing C node in the tree! The ACSL is in an
     *             unexpected and most probably unreachable location and should
     *             be ignored!
     */
    public abstract NextACSL nextACSLStatement() throws ParseException;

    /**
     * Report a syntax error to Ultimate. This will cancel the toolchain.
     * 
     * @param loc
     *            where did it happen?
     * @param type
     *            why did it happen?
     * @param msg
     *            description.
     */
    public static void error(ILocation loc, SyntaxErrorType type, String msg) {
        SyntaxErrorResult<ILocation> result = 
        		new SyntaxErrorResult<ILocation>(loc,
        		Activator.s_PLUGIN_NAME,
        		UltimateServices.getInstance().getTranslatorSequence(),
        		loc, type);
        result.setLongDescription(msg);
        UltimateServices us = UltimateServices.getInstance();
        us.getLogger(Activator.s_PLUGIN_ID).warn(msg);
        us.reportResult(Activator.s_PLUGIN_ID, result);
        us.cancelToolchain();
    }

    /**
     * Report a warning to Ultimate.
     * 
     * @param loc
     *            where did it happen?
     * @param type
     *            why did it happen?
     * @param msg
     *            description.
     */
    public static void warn(ILocation loc, String msg) {
    	String shortDescription = "GenericWarning";
        GenericResult<ILocation> result = 
        		new GenericResult<ILocation>(loc,
                Activator.s_PLUGIN_NAME,
                UltimateServices.getInstance().getTranslatorSequence(),
        		loc, shortDescription, msg, GenericResult.Severity.WARNING);
        UltimateServices us = UltimateServices.getInstance();
        us.getLogger(Activator.s_PLUGIN_ID).warn(msg);
        if (!notifyUltimate)
            return;
        us.reportResult(Activator.s_PLUGIN_ID, result);
    }

//    /**
//     * Report a unknown issue to Ultimate.
//     * 
//     * @param loc
//     *            where did it happen?
//     * @param longDesc
//     *            description.
//     * @param shortDesc
//     *            the short description.
//     */
//    public static void unknown(ILocation loc, String longDesc, String shortDesc) {
//        UnprovableResult<ILocation> result = 
//        		new UnprovableResult<ILocation>(loc,
//                Activator.s_PLUGIN_NAME,
//                UltimateServices.getInstance().getTranslatorSequence(),		
//        		loc);
//        result.setLongDescription(longDesc);
//        result.setShortDescription(shortDesc);
//        UltimateServices us = UltimateServices.getInstance();
//        if (us.getLogger(Activator.s_PLUGIN_ID).isInfoEnabled()) {
//            us.getLogger(Activator.s_PLUGIN_ID).info(longDesc);
//        } else {
//            us.getLogger(Activator.s_PLUGIN_ID).warn(longDesc);
//        }
//        if (!notifyUltimate)
//            return;
//        us.reportResult(Activator.s_PLUGIN_ID, result);
//    }
    
    
    /**
     * Report possible source of unsoundness to Ultimate.
     * 
     * @param loc
     *            where did it happen?
     * @param longDesc
     *            description.
     * @param shortDesc
     *            the short description.
     */
    public static void unsoundnessWarning(ILocation loc, String longDesc, String shortDesc) {
        GenericResult<ILocation> result = 
        		new GenericResult<ILocation>(loc,
                Activator.s_PLUGIN_NAME,
                UltimateServices.getInstance().getTranslatorSequence(),
        		loc, shortDesc, longDesc, GenericResult.Severity.WARNING);
        UltimateServices us = UltimateServices.getInstance();
        if (us.getLogger(Activator.s_PLUGIN_ID).isInfoEnabled()) {
            us.getLogger(Activator.s_PLUGIN_ID).info(longDesc);
        } else {
            us.getLogger(Activator.s_PLUGIN_ID).warn(longDesc);
        }
        if (!notifyUltimate)
            return;
        us.reportResult(Activator.s_PLUGIN_ID, result);
    }

    /**
     * Getter for the setting: checked method.
     * 
     * @return the checked method's name.
     */
    public String getCheckedMethod() {
        IEclipsePreferences prefs = ConfigurationScope.INSTANCE
                .getNode(Activator.s_PLUGIN_ID);
        String checkMethod = SFO.EMPTY;
        try {
            checkMethod = prefs.get(PreferencePage.NAME_MAINPROC, checkMethod);
        } catch (Exception e) {
            throw new IllegalArgumentException(
                    "Unable to determine specified checked method.");
        }
        return checkMethod;
    }
    
    /**
     * Whether the memory model is required or not.
     * 
     * @return whether the memory model is required or not.
     */
    public abstract boolean isMMRequired();

    /**
     * Getter for the identifier mapping.
     * 
     * @return the mapping of Boogie identifiers to origin C identifiers.
     */
    public Map<String, String> getIdentifierMapping() {
        return (cHandler.getSymbolTable().getIdentifierMapping());
    }
    
	/**
	 * TODO: Doku
	 */
	public static List<HavocStatement> createHavocsForAuxVars( 
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		ArrayList<HavocStatement> result = new ArrayList<HavocStatement>();
		for (VariableDeclaration varDecl  : auxVars.keySet()) {
			VarList[] varLists = varDecl.getVariables();
			for (VarList varList : varLists) {
				for(String varId : varList.getIdentifiers()) {
					CACSLLocation originloc = auxVars.get(varDecl); 
					result.add( new HavocStatement(
							originloc, new String[] { varId }));
				}
			}
		}
		return result;
	}
	
	/**
	 * Returns true iff all auxvars in decls are contained in auxVars
	 */
	public boolean isAuxVarMapcomplete(List<Declaration> decls,
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		boolean result = true;
		for (Declaration rExprdecl : decls) {
			assert (rExprdecl instanceof VariableDeclaration);
			VariableDeclaration varDecl = (VariableDeclaration) rExprdecl;
			if (onlyAuxVars((VariableDeclaration) rExprdecl)) {
				result &= auxVars.containsKey(varDecl);
			}
		}
		return result;
	}
	
	/**
	 * Returns true if varDecl contains only auxiliary variables,
	 * returns false if varDecl contrains only non-auxiliary variables,
	 * throws Exception otherwise
	 */
	private boolean onlyAuxVars(VariableDeclaration varDecl) {
		int aux = 0;
		int nonAux = 0;
		for (VarList varLists : varDecl.getVariables()) {
			for (String id : varLists.getIdentifiers() ) {
				if (nameHandler.isTempVar(id)) {
					aux++;
				} else {
					nonAux++;
				}
			}
		}
		if (aux > 0 && nonAux > 0) {
			throw new AssertionError();
		} else {
			assert (aux > 0 || nonAux > 0);
			return aux > 0;
		}
	}
}
