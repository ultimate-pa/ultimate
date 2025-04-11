package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.LocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Simple wrapper of {@link LocalProgramVar} to distinguish AuxVariables when creating updates
 */
public class AuxProgramVar extends LocalProgramVar {
	private static final long serialVersionUID = 1L;

	public AuxProgramVar(final ILocalProgramVar auxProgVar) {
		super(auxProgVar.getIdentifier(), auxProgVar.getProcedure(), auxProgVar.getTermVariable(),
				auxProgVar.getDefaultConstant(), auxProgVar.getPrimedConstant());
	}

	private static final HashMap<String, Integer> usedNames = new HashMap<>();

	private static String getDistinctName(final String name) {
		int version = usedNames.getOrDefault(name, 0);
		final String outName = name + "_auxvar_v" + version;
		version++;
		usedNames.put(name, version);
		return outName;
	}

	public static AuxProgramVar makeAuxProgramVariable(final TermVariable auxVar, final ManagedScript script) {
		script.lock(auxVar);
		final ILocalProgramVar auxProgVar = ProgramVarUtils.constructLocalProgramVar(getDistinctName(auxVar.getName()),
				"interpreter", auxVar.getSort(), script, auxVar);
		script.unlock(auxVar);
		return new AuxProgramVar(auxProgVar);
	}
}