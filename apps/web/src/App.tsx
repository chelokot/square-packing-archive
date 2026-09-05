import {
  explorerBoundFor,
  isGridBaseline,
  gridBaselineConfiguration,
} from "@square-packing/domain";
import { ArrowDown, ArrowUpRight, CodeXml, Grid2X2 } from "lucide-react";
import { archive } from "./archive.ts";
import { ClaimsTable } from "./components/ClaimsTable.tsx";
import { CoverageChart } from "./components/CoverageChart.tsx";
import { CoverageMatrix } from "./components/CoverageMatrix.tsx";
import { FormalizationPanel } from "./components/FormalizationPanel.tsx";
import { PackingViewer } from "./components/PackingViewer.tsx";
import { RecordTimeline } from "./components/RecordTimeline.tsx";
import { copy, repositoryUrl } from "./copy.ts";
import { useSelection } from "./selection.ts";

export const App = () => {
  const [selectedCount, selectCount] = useSelection();
  const selectedClaims = archive.claims.filter(
    (claim) => claim.n === selectedCount,
  );
  const archivedConfiguration = archive.configurationData.find(
    ({ n }) => n === selectedCount,
  );
  const selectedBound = explorerBoundFor(archive, selectedCount);
  const baseline =
    selectedBound !== undefined && isGridBaseline(selectedBound)
      ? selectedBound
      : undefined;
  const configuration =
    archivedConfiguration === undefined && baseline !== undefined
      ? gridBaselineConfiguration(baseline)
      : archivedConfiguration;
  const configurationClaim =
    archivedConfiguration === undefined
      ? baseline
      : archive.claims.find(
          (claim) => claim.configuration === archivedConfiguration.id,
        );

  return (
    <div className="min-h-screen bg-paper text-ink">
      <a
        href="#explore"
        className="sr-only focus:not-sr-only focus:fixed focus:left-4 focus:top-4 focus:z-50 focus:bg-paper focus:p-4"
      >
        {copy.skipNavigation}
      </a>
      <header className="border-b border-rule">
        <div className="mx-auto flex max-w-[96rem] flex-wrap items-center justify-between gap-4 px-5 py-5 md:px-10">
          <a
            href="#top"
            className="flex items-center gap-3 font-semibold tracking-tight"
          >
            <Grid2X2
              className="size-6 text-forest"
              strokeWidth={1.5}
              aria-hidden="true"
            />
            <h1>{copy.title}</h1>
          </a>
          <nav
            aria-label={copy.navigation}
            className="flex flex-wrap items-center gap-x-5 gap-y-2 text-sm text-muted md:gap-x-8"
          >
            <a href="#explore" className="hover:text-ink">
              {copy.explore}
            </a>
            <a href="#claims" className="hover:text-ink">
              {copy.catalog}
            </a>
            <a href="#formalization" className="hover:text-ink">
              {copy.sources}
            </a>
            <a
              href={repositoryUrl}
              className="flex items-center gap-1.5 hover:text-ink"
              aria-label={copy.github}
            >
              <CodeXml className="size-4" aria-hidden="true" />
              <span className="hidden sm:inline">{copy.github}</span>
            </a>
          </nav>
        </div>
      </header>
      <main id="top" className="mx-auto max-w-[96rem] px-5 pb-16 md:px-10">
        <p className="py-5 text-sm leading-6 text-muted">{copy.introduction}</p>
        <section
          id="explore"
          aria-label={copy.explore}
          className="scroll-mt-6 pb-8"
        >
          <h2 className="sr-only">{copy.explore}</h2>
          <div className="grid items-start gap-6 lg:grid-cols-[21rem_minmax(0,1fr)]">
            <CoverageMatrix
              archive={archive}
              selectedCount={selectedCount}
              onSelect={selectCount}
            />
            <div className="min-w-0">
              {configuration === undefined ? (
                <section
                  id="viewer"
                  className="flex min-h-[29rem] flex-col items-center justify-center border border-rule bg-surface px-6 py-12 text-center"
                >
                  <p className="font-serif text-6xl">s({selectedCount})</p>
                  <h3 className="mt-6 text-lg font-medium">{copy.noLayout}</h3>
                  <p className="mt-2 max-w-md text-sm leading-6 text-muted">
                    {selectedClaims.length === 0
                      ? copy.noRecord
                      : copy.layoutNotImported}
                  </p>
                  <a
                    href="#history"
                    className="mt-5 inline-flex items-center gap-2 text-sm text-forest"
                  >
                    {copy.readHistory}
                    <ArrowDown className="size-4" aria-hidden="true" />
                  </a>
                  <div className="mt-10 flex flex-wrap justify-center gap-2">
                    {archive.configurationData.map((item) => (
                      <button
                        key={item.id}
                        type="button"
                        onClick={() => selectCount(item.n)}
                        className="border border-rule px-3 py-2 font-mono text-xs hover:border-forest"
                      >
                        {copy.viewLayout(item.n)}
                      </button>
                    ))}
                  </div>
                </section>
              ) : (
                <PackingViewer
                  key={configuration.id}
                  configuration={configuration}
                  claim={configurationClaim}
                />
              )}
            </div>
          </div>
        </section>
        <section id="history" className="scroll-mt-6 border-t border-rule py-8">
          <h2 className="mb-5 flex items-center gap-3 text-lg font-semibold">
            {copy.history}
          </h2>
          <div className="grid items-start gap-8 lg:grid-cols-2">
            <RecordTimeline archive={archive} squareCount={selectedCount} />
            <CoverageChart archive={archive} />
          </div>
        </section>
        <ClaimsTable archive={archive} onSelect={selectCount} />
        <FormalizationPanel archive={archive} />
      </main>
      <footer className="border-t border-rule">
        <div className="mx-auto flex max-w-[96rem] flex-wrap justify-between gap-5 px-5 py-7 text-xs leading-6 text-muted md:px-10">
          <p className="text-xs text-muted">
            {copy.archiveScope(archive.updatedAt)}
          </p>
          <p>
            <a
              className="hover:text-ink"
              href={`${repositoryUrl}/blob/main/LICENSE`}
            >
              {copy.codeLicense}
            </a>
            <span className="mx-2">·</span>
            <a
              className="hover:text-ink"
              href={`${repositoryUrl}/blob/main/LICENSE-DATA`}
            >
              {copy.dataLicense}
            </a>
          </p>
          <a
            href={`${repositoryUrl}/blob/main/CONTRIBUTING.md`}
            className="inline-flex items-center gap-1 text-forest"
          >
            {copy.contribute}
            <ArrowUpRight className="size-4" aria-hidden="true" />
          </a>
        </div>
      </footer>
    </div>
  );
};
