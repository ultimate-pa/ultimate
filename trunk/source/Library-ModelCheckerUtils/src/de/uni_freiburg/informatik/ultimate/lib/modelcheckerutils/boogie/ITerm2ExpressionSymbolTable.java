package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public interface ITerm2ExpressionSymbolTable {

	IProgramFunction getProgramFun(FunctionSymbol funSym);

	IProgramVar getProgramVar(TermVariable term);

	Map<String, String> getSmtFunction2BoogieFunction();

	ILocation getLocation(IProgramVar pv);

	DeclarationInformation getDeclarationInformation(IProgramVar pv);

}
