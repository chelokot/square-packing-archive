import { z } from "zod";

const identifier = z.string().regex(/^[a-z0-9]+(?:-[a-z0-9]+)*$/);
const date = z.string().regex(/^\d{4}(?:-\d{2}(?:-\d{2})?)?$/);
const decimal = z.string().regex(/^\d+(?:\.\d+)?$/);
const leanArtifactSchema = z
  .string()
  .regex(/^formal\/SquarePackingArchive(?:\/[A-Za-z0-9_]+)+\.lean$/);
const leanTheoremSchema = z
  .string()
  .regex(/^SquarePackingArchive(?:\.[A-Za-z_][A-Za-z0-9_']*)+$/);

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
  lean: z.string().min(1).optional(),
  polynomial: z.string().min(1).optional(),
});

export const contributorSchema = z.object({
  author: identifier,
  role: z.enum(["discoverer", "discoverer-and-prover", "optimizer", "prover"]),
});

export const evidenceSchema = z
  .object({
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
    checkedAt: z.iso.date().optional(),
  })
  .superRefine((evidence, context) => {
    if (evidence.kind === "lean-proof") {
      if (evidence.status !== "lean-checked") {
        context.addIssue({
          code: "custom",
          message: "Lean evidence must be lean-checked",
          path: ["status"],
        });
      }
      for (const field of ["artifact", "theorem", "checkedAt"] as const) {
        if (evidence[field] === undefined) {
          context.addIssue({
            code: "custom",
            message: `Lean evidence requires ${field}`,
            path: [field],
          });
        }
      }
      for (const [field, schema] of [
        ["artifact", leanArtifactSchema],
        ["theorem", leanTheoremSchema],
      ] as const) {
        if (
          evidence[field] !== undefined &&
          !schema.safeParse(evidence[field]).success
        ) {
          context.addIssue({
            code: "custom",
            message: `Invalid Lean ${field}`,
            path: [field],
          });
        }
      }
    } else if (evidence.status === "lean-checked") {
      context.addIssue({
        code: "custom",
        message: "Only Lean evidence can be lean-checked",
        path: ["status"],
      });
    }
    if (evidence.kind !== "lean-proof" && evidence.checkedAt !== undefined) {
      context.addIssue({
        code: "custom",
        message: "Only Lean evidence can declare checkedAt",
        path: ["checkedAt"],
      });
    }
  });

export const claimSchema = z
  .object({
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
  })
  .superRefine((claim, context) => {
    if (
      claim.value.lean === undefined &&
      claim.evidence.some((evidence) => evidence.kind === "lean-proof")
    ) {
      context.addIssue({
        code: "custom",
        message: "Lean-verified claim requires value.lean",
        path: ["value", "lean"],
      });
    }
  });

export const catalogClaimSchema = claimSchema.refine(
  (claim) => claim.evidence.some((evidence) => evidence.kind === "lean-proof"),
  {
    message:
      "Catalog claims require a Lean proof; keep unformalized proposals in issues",
    path: ["evidence"],
  },
);

export const configurationReferenceSchema = z.union([
  z.object({
    id: identifier,
    path: z.string().regex(/^configurations\/[a-z0-9-]+\.json$/),
  }),
  z
    .object({
      id: identifier,
      recipe: z.literal("grid"),
      n: z.number().int().positive(),
      side: z.number().int().positive(),
    })
    .refine(({ n, side }) => n <= side * side, "Grid capacity exceeded"),
  z.object({
    id: identifier,
    recipe: z.literal("goebel"),
    n: z.union([z.literal(5), z.literal(10)]),
  }),
  z
    .object({
      id: identifier,
      recipe: z.literal("goebel-strip"),
      steps: z.number().int().positive(),
      stripCount: z.number().int().positive(),
    })
    .refine(
      ({ steps, stripCount }) =>
        BigInt(stripCount - 1) ** 2n <= 2n * BigInt(steps - 1) ** 2n,
      "Diagonal strip exceeds available length",
    ),
]);

export const manifestSchema = z.object({
  schemaVersion: z.literal(1),
  updatedAt: date,
  gridBaseline: z
    .object({
      through: z.number().int().positive().max(100),
      proof: z.object({
        source: identifier,
        artifact: leanArtifactSchema,
        theorem: leanTheoremSchema,
        checkedAt: z.iso.date(),
      }),
    })
    .optional(),
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
  denominator: z.string().regex(/^[1-9]\d*$/),
});

export const quadraticSchema = z.object({
  rational: ratioSchema,
  sqrtTwo: ratioSchema,
});

export const exactNumberSchema = z.union([ratioSchema, quadraticSchema]);

export const squareSchema = z.object({
  id: z.number().int().nonnegative(),
  center: z.object({ x: exactNumberSchema, y: exactNumberSchema }),
  orientation: z.object({
    tangentHalfAngle: exactNumberSchema,
    cosine: exactNumberSchema,
    sine: exactNumberSchema,
    angleRadiansApprox: z.number().finite(),
  }),
});

export const packingConfigurationSchema = z.object({
  schemaVersion: z.literal(1),
  id: identifier,
  n: z.number().int().positive(),
  containerSide: z.union([
    ratioSchema.extend({ decimal }),
    quadraticSchema.extend({ decimal }),
  ]),
  coordinateSystem: z.literal("physical-cartesian-bottom-left"),
  squareSide: ratioSchema,
  squares: z.array(squareSchema),
  certificate: z.object({
    method: z.enum([
      "exact-rational-separating-axis",
      "exact-quadratic-separating-axis",
    ]),
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
  claims: z.array(catalogClaimSchema),
  configurationData: z.array(packingConfigurationSchema),
});

export type ArchiveManifest = z.infer<typeof manifestSchema>;
export type Author = z.infer<typeof authorSchema>;
export type Claim = z.infer<typeof claimSchema>;
export type CompiledArchive = z.infer<typeof compiledArchiveSchema>;
export type Evidence = z.infer<typeof evidenceSchema>;
export type PackingConfiguration = z.infer<typeof packingConfigurationSchema>;
export type Ratio = z.infer<typeof ratioSchema>;
export type ExactNumber = z.infer<typeof exactNumberSchema>;
export type Source = z.infer<typeof sourceSchema>;
