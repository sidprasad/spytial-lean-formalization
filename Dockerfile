FROM leanprover/lean4:v4.24.0

WORKDIR /lean-mech

# Copy project files and fetch Mathlib cache before copying source
# (cache layer is invalidated only if dependencies change)
COPY lean-toolchain lakefile.lean lake-manifest.json ./
RUN lake exe cache get && lake build

# Copy source and build script
COPY Main.lean check.sh entrypoint.sh ./
RUN chmod +x check.sh entrypoint.sh

EXPOSE 8080

CMD ["./entrypoint.sh"]
