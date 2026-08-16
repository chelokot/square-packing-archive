import { z } from "zod";

const identifier = z.string().regex(/^[a-z0-9]+(?:-[a-z0-9]+)*$/);
const date = z.string().regex(/^\d{4}(?:-\d{2}(?:-\d{2})?)?$/);
const decimal = z.string().regex(/^\d+(?:\.\d+)?$/);

export const linkSchema = z.object({
  label: z.string().min(1),
  url: z.url(),
});

export const authorSchema = z.object({
  id: identifier,
  name: z.string().min(1),
  links: z.array(linkSchema).optional(),
});

export const sourceSchema = z.object({
  id: identifier,
  kind: z.enum(["publication", "preprint", "repository", "tracker"]),
  title: z.string().min(1),
  authors: z.array(identifier),
  url: z.url(),
  publishedAt: date.optional(),
  accessedAt: date.optional(),
});

export const valueSchema = z.object({
  decimal,
  expression: z.string().min(1).optional(),
  polynomial: z.string().min(1).optional(),
});

export const contributorSchema = z.object({
  author: identifier,
  role: z.enum(["discoverer", "discoverer-and-prover", "optimizer", "prover"]),
});

export const evidenceSchema = z.object({
  kind: z.enum([
    "elementary-construction",
    "elementary-proof",
    "interval-certificate",
    "lean-proof",
    "published-proof",
    "tracker-record",
  ]),
  status: z.enum([
    "computationally-checked",
    "lean-checked",
    "published",
    "reported",
  ]),
  source: identifier,
  artifact: z.string().min(1).optional(),
  theorem: z.string().min(1).optional(),
});

export const claimSchema = z.object({
  id: identifier,
  n: z.number().int().positive(),
  relation: z.enum(["exact", "lower", "upper"]),
  value: valueSchema,
  announcedAt: date,
  contributors: z.array(contributorSchema),
  evidence: z.array(evidenceSchema).min(1),
  configuration: identifier.optional(),
  supersedes: identifier.optional(),
  active: z.boolean(),
});

export const configurationReferenceSchema = z.object({
  id: identifier,
  path: z.string().regex(/^configurations\/[a-z0-9-]+\.json$/),
});

export const manifestSchema = z.object({
  schemaVersion: z.literal(1),
  updatedAt: date,
  problem: z.object({
    symbol: z.literal("s"),
    name: z.string().min(1),
    definition: z.string().min(1),
  }),
  authors: z.array(authorSchema),
  sources: z.array(sourceSchema),
  claims: z.array(claimSchema),
  configurations: z.array(configurationReferenceSchema),
});

export const ratioSchema = z.object({
  numerator: z.string().regex(/^-?\d+$/),
  denominator: z.string().regex(/^\d+$/),
});

export const squareSchema = z.object({
  id: z.number().int().nonnegative(),
  center: z.object({ x: ratioSchema, y: ratioSchema }),
  orientation: z.object({
    tangentHalfAngle: ratioSchema,
    cosine: ratioSchema,
    sine: ratioSchema,
    angleRadiansApprox: z.number().finite(),
  }),
});

export const packingConfigurationSchema = z.object({
  schemaVersion: z.literal(1),
  id: identifier,
  n: z.number().int().positive(),
  containerSide: ratioSchema.extend({ decimal }),
  coordinateSystem: z.literal("physical-cartesian-bottom-left"),
  squareSide: ratioSchema,
  squares: z.array(squareSchema),
  certificate: z.object({
    method: z.literal("exact-rational-separating-axis"),
    minimumContainmentMargin: ratioSchema,
    minimumSeparationMargin: ratioSchema,
    orientationReconstruction: z.string().min(1),
  }),
  provenance: z.object({
    source: z.string().min(1),
    sourceOptimizedContainerSide: decimal,
    importedAt: date,
  }),
});

export const compiledArchiveSchema = manifestSchema.extend({
  configurationData: z.array(packingConfigurationSchema),
});

export type ArchiveManifest = z.infer<typeof manifestSchema>;
export type Author = z.infer<typeof authorSchema>;
export type Claim = z.infer<typeof claimSchema>;
export type CompiledArchive = z.infer<typeof compiledArchiveSchema>;
export type Evidence = z.infer<typeof evidenceSchema>;
export type PackingConfiguration = z.infer<typeof packingConfigurationSchema>;
export type Ratio = z.infer<typeof ratioSchema>;
export type Source = z.infer<typeof sourceSchema>;
