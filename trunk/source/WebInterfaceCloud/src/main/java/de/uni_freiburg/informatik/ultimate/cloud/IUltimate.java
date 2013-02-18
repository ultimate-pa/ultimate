package de.uni_freiburg.informatik.ultimate.cloud;

import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;

public interface IUltimate   {

	IResult getResult(String id);
	
	void startUltimate(String taskName, String settingsFile, Toolchain toolchain, String code);
}
