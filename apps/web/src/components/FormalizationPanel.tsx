import type { CompiledArchive } from "@square-packing/domain";
import { ArrowUpRight } from "lucide-react";
import { copy, repositoryUrl } from "../copy.ts";

export const FormalizationPanel = ({
  archive,
}: {
  archive: CompiledArchive;
}) => (
  <section
    id="formalization"
    className="grid gap-10 border-t border-rule py-10 lg:grid-cols-[1fr_1.4fr]"
  >
    <div>
      <h2 className="font-serif text-2xl">{copy.proofTitle}</h2>
      <p className="mt-4 max-w-xl text-sm leading-7 text-muted">
        {copy.proofDescription}
      </p>
      <div className="mt-5 flex flex-wrap gap-x-6 gap-y-3 text-sm text-forest">
        <a
          href={`${repositoryUrl}/tree/main/formal`}
          className="inline-flex items-center gap-1"
        >
          {copy.proofLink}
          <ArrowUpRight className="size-4" aria-hidden="true" />
        </a>
        <a href={`${repositoryUrl}/blob/main/archive/manifest.json`}>
          {copy.dataLink}
        </a>
        <a href={`${repositoryUrl}/issues`}>{copy.pendingResults}</a>
      </div>
    </div>
    <div>
      <h2 className="font-serif text-2xl">{copy.sourcesTitle}</h2>
      <p className="mt-4 text-sm leading-7 text-muted">
        {copy.sourcesDescription}
      </p>
      <ul className="mt-5 divide-y divide-rule">
        {archive.sources
          .filter(
            (source) =>
              source.kind === "tracker" ||
              source.kind === "publication" ||
              source.kind === "preprint",
          )
          .map((source) => (
            <li key={source.id} className="py-3">
              <a
                href={source.url}
                className="group flex items-baseline justify-between gap-4 text-sm hover:text-forest"
              >
                <span>
                  {source.title}
                  <span className="mt-1 block text-xs text-muted">
                    {source.authors
                      .map(
                        (id) =>
                          archive.authors.find((author) => author.id === id)!
                            .name,
                      )
                      .join(", ")}
                  </span>
                </span>
                <span className="flex shrink-0 items-center gap-2 font-mono text-xs text-muted">
                  {source.publishedAt}
                  <ArrowUpRight
                    className="size-3.5 group-hover:text-forest"
                    aria-hidden="true"
                  />
                </span>
              </a>
            </li>
          ))}
      </ul>
    </div>
  </section>
);
