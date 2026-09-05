from pathlib import Path
import subprocess


def main() -> None:
    formal = Path(__file__).resolve().parents[1] / "formal"
    for artifact in sorted((formal / "SquarePackingArchive" / "Records").glob("*.lean")):
        if artifact.read_text().startswith("import SquarePackingArchive.QuadraticCertificate\n"):
            module = ".".join(artifact.relative_to(formal).with_suffix("").parts)
            subprocess.run(["lake", "--wfail", "build", module], cwd=formal, check=True)
    subprocess.run(["lake", "--wfail", "build"], cwd=formal, check=True)


if __name__ == "__main__":
    main()
