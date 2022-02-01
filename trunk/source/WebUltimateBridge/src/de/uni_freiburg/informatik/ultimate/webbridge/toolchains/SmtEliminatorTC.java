/**
 * Boogie TraceAbstraction toolchain.
 */
package de.uni_freiburg.informatik.ultimate.webbridge.toolchains;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.webbridge.website.Setting;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.webbridge.website.Tool;
import de.uni_freiburg.informatik.ultimate.webbridge.website.WebToolchain;

/**
 * @author @author Matthias Heizmann
 */
public class SmtEliminatorTC extends WebToolchain {

	@Override
	protected String defineDescription() {
		return NameStrings.TOOL_ELIMINATOR;
	}

	@Override
	protected String defineName() {
		return NameStrings.TOOL_ELIMINATOR;
	}

	@Override
	protected String defineId() {
		return "smtEliminator";
	}

	@Override
	protected TaskNames[] defineTaskName() {
		return new TaskNames[] { TaskNames.ELIMINATOR_SMT };
	}

	@Override
	protected String defineLanguage() {
		return "smt";
	}

	@Override
	protected String defineUserInfo() {
		return null;
	}

	@Override
	protected String defineInterfaceLayoutFontsize() {
		return PrefStrings.INTERFACE_LAYOUT_FONTSIZE_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutOrientation() {
		return PrefStrings.INTERFACE_LAYOUT_ORIENTATION_DEFAULT;
	}

	@Override
	protected String defineInterfaceLayoutTransitions() {
		return PrefStrings.INTERFACE_LAYOUT_TRANSITION_DEFAULT;
	}

	@Override
	protected List<Tool> defineTools() {
		return Collections.emptyList();
	}

	@Override
	protected List<Setting> defineAdditionalSettings() {
		return Collections.emptyList();
	}

	@Override
	protected String defineToolchainSettingsFile() {
		return "Eliminator.epf";
	}

}
