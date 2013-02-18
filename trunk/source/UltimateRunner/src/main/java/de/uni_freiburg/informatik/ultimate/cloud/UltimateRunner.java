package de.uni_freiburg.informatik.ultimate.cloud;

import java.io.BufferedWriter;
import java.io.FileWriter;



public class UltimateRunner {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		System.out.print("Test");
		
		try
		{
			FileWriter fileWriter = new FileWriter("result.txt");
			BufferedWriter out = new BufferedWriter(fileWriter);
			out.write("test");
			out.close();	
		
		} catch (Exception e) {
			System.out.print("false");
		}
		
		
		/*Application app = new Application(Ultimate_Mode.EXTERNAL_EXECUTION);
		
		File codeFile = new File("code");
		app.setM_InputFile(codeFile);
		
		File toolchain = new File("toolchain.xml");
		app.setToolchainXML(toolchain);
		
		File settings = new File("settings.xml");
		app.setSettingsFile(settings);
		
		try {
			app.start(null);
		} catch (Throwable t) {

			System.out.print("false");
		}
		
		// get Result from Ultimate
		UltimateServices us = UltimateServices.getInstance();
		HashMap<String, List<IResult>> results = us.getResultMap();
		
		// add result to the json object
		JSONObject json = new JSONObject();
		ArrayList<JSONObject> resultList = new ArrayList<JSONObject>();
		for (List<IResult> rList : results.values()) {
			for (IResult r : rList) {
				String type = "UNDEF";
				UltimateResult packagedResult = new UltimateResult();
				if (r instanceof CounterExampleResult) {
					type = "counter";
					packagedResult.logLvl = "error";
				} else if (r instanceof InvariantResult) {
					type = "invariant";
					packagedResult.logLvl = "info";
				} else if (r instanceof PositiveResult) {
					type = "positive";
					packagedResult.logLvl = "info";
				} else if (r instanceof UnprovableResult) {
					type = "unprovable";
					packagedResult.logLvl = "warning";
				} else if (r instanceof SyntaxErrorResult) {
					type = "syntaxError";
					packagedResult.logLvl = "error";
				} else if (r instanceof TimeoutResult) {
					type = "timeout";
					packagedResult.logLvl = "error";
				} // TODO : Add new "Out of resource" result here ...
				Location loc = r.getLocation();
				packagedResult.shortDesc = r.getShortDescription();
				packagedResult.longDesc = r.getLongDescription();
				packagedResult.startLNr = loc.getStartLine();
				packagedResult.endLNr = loc.getEndLine();
				packagedResult.startCol = loc.getStartColumn();
				packagedResult.endCol = loc.getEndColumn();
				packagedResult.type = type;
				resultList.add(new JSONObject(packagedResult));
			}
			json.put("results", new JSONArray(resultList.toArray(new JSONObject[0])));
		}
		
		//Write Results to a file
		FileWriter fileWriter = new FileWriter("result.txt");
		BufferedWriter out = new BufferedWriter(new FileWriter(resultFile));
		out.write(json.toString());
		out.close();*/
	}

}
