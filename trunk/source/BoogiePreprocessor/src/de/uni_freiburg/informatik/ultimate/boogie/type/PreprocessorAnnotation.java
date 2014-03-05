package de.uni_freiburg.informatik.ultimate.boogie.type;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;

/**
 * 
 * @author dietsch
 *
 */
public class PreprocessorAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	private BoogieSymbolTable mSymbolTable;

	public BoogieSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public void setSymbolTable(BoogieSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
	}

	public void annotate(IElement elem) {
		if(elem == null){
			return;
		}
		elem.getPayload().getAnnotations().put(Activator.PLUGIN_ID, this);
	}

	public static PreprocessorAnnotation getAnnotation(IElement elem) {
		if (elem.hasPayload() && elem.getPayload().hasAnnotation()) {
			return (PreprocessorAnnotation) elem.getPayload().getAnnotations().get(Activator.PLUGIN_ID);
		}
		return null;
	}

	@Override
	protected String[] getFieldNames() {
		return new String[] { "SymbolTable" };
	}

	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "SymbolTable":
			return mSymbolTable;
		default:
			return null;
		}
	}

}
