package de.uni_freiburg.informatik.ultimate.core.lib.results.dto;

import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifDTO;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifDriver;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifMessage;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifRun;
import de.uni_freiburg.informatik.ultimate.core.lib.results.dto.sarif.SarifTool;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchain;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public final class SarifDTOMapper implements IResultDTOMapper<SarifDTO> {

	@Override
	public SarifDTO transform(final IToolchain<RunDefinition> toolchain, final ICore<RunDefinition> core,
			final Map<String, List<IResult>> results) {

		final SarifDriver sDriver = new SarifDriver("Ultimate Automizer");
		final SarifTool stool = new SarifTool(sDriver);

		final List<SarifResult> sResults = results.entrySet().stream().flatMap(x -> x.getValue().stream())
				.map(x -> ultimateResultToSarifResult(x)).toList();
		final SarifRun srun = new SarifRun(stool, sResults);
		return new SarifDTO(List.of(srun));
	}

	private static SarifResult ultimateResultToSarifResult(final IResult res) {
		String ruleId = "NO_RULE_ID";
		if (res instanceof final PositiveResult<?> posRes) {
			ruleId = posRes.getCheckedSpecification().getSpec().toString();
		}
		if (res instanceof final CounterExampleResult ctxRes) {
			ruleId = ctxRes.getCheckedSpecification().getSpec().toString();
		}

		return new SarifResult(ruleId, new SarifMessage(res.getShortDescription()));
	}
}
